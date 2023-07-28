/*
 * Copyright © 2023 Matthew Wozniak <sirtomato999@gmail.com>
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED “AS IS” AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
 * REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
 * INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
 * LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
 * OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
 * PERFORMANCE OF THIS SOFTWARE.
 */

#include <stdlib.h>
#include <string.h>

#include "con_.h"
#include "engineapi.h"
#include "errmsg.h"
#include "gametype.h"
#include "gamedata.h"
#include "feature.h"
#include "hook.h"
#include "intdefs.h"
#include "mem.h"
#include "os.h"
#include "ppmagic.h"
#include "sst.h"
#include "vcall.h"
#include "x86.h"
#include "x86util.h"

FEATURE("timescale")

REQUIRE_GAMEDATA(vtidx_RunFrame)
REQUIRE_GAMEDATA(vtidx_Frame)

typedef void (*Host_AccumulateTime_func)(float dt);
static Host_AccumulateTime_func orig_Host_AccumulateTime;
float *realtime;
float *host_frametime;

static float skiptime = 0.0;
void hook_Host_AccumulateTime(float dt) {
	if (skiptime > 0.) {
		*realtime += skiptime;
		*host_frametime += skiptime;
		skiptime = 0.0;
	} else {
		orig_Host_AccumulateTime(dt);
	}
}

DEF_CCMD_HERE(sst_fastforward, "Fast forward a certain amount of time", CON_DEMO) {
	if (cmd->argc != 2) {
		con_warn("usage: sst_fastforward <time>");
		return;
	}
	skiptime = (float)atof(cmd->argv[1]);
}

// we can find some float globals with functions that return them immediately
// FLD dword ptr [floatvar]
float *floatgetter(void *fn) {
	uchar *inst = (uchar *)fn;
	if (inst[0] != X86_FLTBLK2 || inst[1] != 0x05) return NULL;
	else return (float *)mem_loadptr(inst + 2);
}

// a few layers of the call stack only have the target function take any float
// args so we can just look for an FLD and grab the next call after that
void *find_floatcall(void *fn, const char *name) {
	const uchar *ins = (const uchar *)fn;
	bool nextcall = false;
	for (const uchar *p = ins; p - ins < 384;) {
		if (p[0] == X86_FLTBLK2 && (p[1] & 0x38) == 0) {
			nextcall = true;
		} else if (nextcall && p[0] == X86_CALL) {
			int offset = (int)mem_load32(p + 1);
			return (void*)(p + x86_len(p) + offset);
		}
		NEXT_INSN(p, name);
	}
	return NULL;
}

// find Host_AccumulateTime
bool find_Host_AccumulateTime(void) {
	// start with CDedicatedServerAPI::RunFrame
	void *runframe = NULL;
	{
		void ***hldsapi = factory_engine("VENGINE_HLDS_API_VERSION002", NULL);
		if (!hldsapi) {
			errmsg_errorx("missing hlds api interface");
		}
		runframe = (*hldsapi)[vtidx_RunFrame];
	}
	// This function first calls a virtual function on `eng`, the CEngine
	// global. Look for the thisptr load into ECX
	void *frame = NULL;
	{
		void ***eng = NULL;
		const uchar *ins = (const uchar *)runframe;
		for (const uchar *p = ins; p - ins < 32;) {
			// mov ecx, dword ptr [this]
			if (p[0] == X86_MOVRMW && p[1] == X86_MODRM(0, 1, 5)) {
				void **indirect = mem_loadptr(p + 2);
				eng = *indirect;
				break;
			}
			NEXT_INSN(p, "eng global object");
		}
		if (!eng) {
			errmsg_errorx("couldn't find eng global object");
			return false;
		}
		frame = (*eng)[vtidx_Frame];
	}
	// this function is called inside a switch case which gets simplified to a
	// simple if, so we search for the `cmp` and then the next CALL
	void *hoststate_frame = NULL;
	{
		const uchar *ins = (const uchar *)frame;
		bool nextcall = false;
		for (const uchar *p = ins; p - ins < 384;) {
			if (p[0] == X86_ALUMI8S && (p[1] & 0x38) == X86_MODRM(0, 7, 0) && p[2] == 2) {
				nextcall = true;
			} else if (nextcall && p[0] == X86_CALL) {
				// basic x86 call is relative to the end of the call inst
				int offset = (int)mem_load32(p + 1);
				hoststate_frame = (void *)(p + x86_len(p) + offset);
				break;
			}
			NEXT_INSN(p, "HostState_Frame");
		}
		if (!hoststate_frame) {
			errmsg_errorx("couldn't find HostState_Frame");
			return false;
		}
	}
	// HostState_Frame contains only another CALL to a class function (not
	// virtual)
	void *frameupdate = NULL;
	{
		const uchar *ins = (const uchar *)hoststate_frame;
		for (const uchar *p = ins; p - ins < 384;) {
			if (p[0] == X86_CALL) {
				// basic x86 call is relative to the end of the call inst
				int offset = (int)mem_load32(p + 1);
				frameupdate = (void*)(p + x86_len(p) + offset);
				break;
			}
			NEXT_INSN(p, "CHostState::FrameUpdate");
		}
		if (!frameupdate) {
			errmsg_errorx("couldn't find frameupdate");
			return false;
		}
	}
	// CHostState::State_Run is the only function called here that takes a float
	// as an arg so we can just search for the float ops here.
	void *state_run = find_floatcall(frameupdate, "CHostState::State_Run");
	if (!state_run) {
		errmsg_errorx("couldn't find State_Run");
		return false;
	}

	void *host_runframe = find_floatcall(state_run, "Host_RunFrame");
	if (!host_runframe) {
		errmsg_errorx("couldn't find Host_RunFrame");
		return false;
	}

	void *_host_runframe = find_floatcall(host_runframe, "_Host_RunFrame");
	if (!_host_runframe) {
		errmsg_errorx("couldn't find _Host_RunFrame");
		return false;
	}

	// here we want the function that passes in the time arg
	const uchar *ins = (const uchar *)_host_runframe;
	bool nextcall = false;
	for (const uchar *p = ins; p - ins < 384;) {
		if (p[0] == X86_FLTBLK2 && p[1] == X86_MODRM(1, 0, 5) && p[2] == 8) {
			nextcall = true;
		} else if (nextcall && p[0] == X86_CALL) {
			int offset = (int)mem_load32(p + 1);
			orig_Host_AccumulateTime =
				(Host_AccumulateTime_func)(p + x86_len(p) + offset);
			break;
		}
		NEXT_INSN(p, "Host_AccumulateTime");
	}
	if (!orig_Host_AccumulateTime) {
		errmsg_errorx("couldn't find Host_AccumulateTime");
		return false;
	}
	return true;
}

PREINIT {
	return true;
}

INIT {
	// use this interface to get the float globals
	void ***enginetool = factory_engine("VENGINETOOL003", NULL);
	if (!enginetool) {
		errmsg_errorx("missing engine tool interface");
		return false;
	}
	realtime = floatgetter((*enginetool)[vtidx_GetRealTime]);
	host_frametime = floatgetter((*enginetool)[vtidx_HostFrameTime]);
	if (!find_Host_AccumulateTime()) {
		errmsg_errorx("couldn't find Host_Accumulate");
		return false;
	}
	orig_Host_AccumulateTime = (Host_AccumulateTime_func)hook_inline(
			(void*)orig_Host_AccumulateTime, (void*)hook_Host_AccumulateTime);
	return true;
}

END {
	unhook_inline((void*)orig_Host_AccumulateTime);
}

// vi: sw=4 ts=4 noet tw=80 cc=80
