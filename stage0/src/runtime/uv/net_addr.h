/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Henrik Böving
*/
#pragma once
#include <lean/lean.h>
#include "runtime/object.h"

namespace lean {

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>

void lean_ipv4_addr_to_in_addr(b_obj_arg ipv4_addr, struct in_addr* out);
void lean_ipv6_addr_to_in6_addr(b_obj_arg ipv6_addr, struct in6_addr* out);
lean_obj_res lean_in_addr_to_ipv4_addr(const struct in_addr* ipv4_addr);
lean_obj_res lean_in6_addr_to_ipv6_addr(const struct in6_addr* ipv6_addr);

#endif

extern "C" LEAN_EXPORT lean_obj_res lean_uv_pton_v4(b_obj_arg str_obj);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ntop_v4(b_obj_arg ipv4_addr);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_pton_v6(b_obj_arg str_obj);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ntop_v6(b_obj_arg ipv6_addr);

}
