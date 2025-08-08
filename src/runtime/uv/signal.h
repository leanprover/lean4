/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/uv/event_loop.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {

// =======================================
// Signal functions

extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_wait(uint32_t signum_obj, obj_arg /* w */);

}
