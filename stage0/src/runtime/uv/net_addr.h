/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Henrik Böving
*/
#pragma once
#include <lean/lean.h>
#include "runtime/object.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

void lean_socket_address_to_sockaddr_storage(b_obj_arg socket_addr, sockaddr_storage* out);
void lean_ip_addr_ntop(b_obj_arg ip_addr, char* buffer, size_t buffer_size);

// `addr` points to an `in_addr` if `family` is `AF_INET`, and to an `in6_addr` if it is `AF_INET6`.
lean_obj_res lean_in_addr_to_ip_addr(int family, const void* addr);
lean_obj_res lean_sockaddr_to_socketaddress(const sockaddr* sa);

#endif

extern "C" LEAN_EXPORT lean_obj_res lean_uv_pton_v4(b_obj_arg str_obj);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ntop_v4(b_obj_arg ipv4_addr);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_pton_v6(b_obj_arg str_obj);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ntop_v6(b_obj_arg ipv6_addr);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_interface_addresses();

}
