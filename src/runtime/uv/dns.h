/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/uv/event_loop.h"
#include "runtime/uv/net_addr.h"

namespace lean {

#ifndef LEAN_EMSCRIPTEN
using namespace std;
#include <uv.h>

#endif

// =======================================
// DNS functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_dns_get_info(b_obj_arg name, b_obj_arg service, uint8_t family);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_dns_get_name(b_obj_arg ip_addr);

}
