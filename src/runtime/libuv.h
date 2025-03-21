/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Markus Himmel, Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/uv/event_loop.h"
#include "runtime/uv/timer.h"
#include "runtime/uv/tcp.h"
#include "runtime/uv/udp.h"
#include "runtime/alloc.h"
#include "runtime/io.h"
#include "runtime/utf8.h"
#include "runtime/object.h"
#include "runtime/thread.h"
#include "runtime/allocprof.h"
#include "runtime/object.h"

namespace lean {
#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

extern "C" void initialize_libuv();

// =======================================
// General LibUV functions.
extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg);

}