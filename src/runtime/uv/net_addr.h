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

typedef union in_addr_storage {
    in_addr ipv4;
    in6_addr ipv6;
} in_addr_storage;

void lean_ipv4_addr_to_in_addr(b_obj_arg ipv4_addr, struct in_addr* out);
void lean_ipv6_addr_to_in6_addr(b_obj_arg ipv6_addr, struct in6_addr* out);
void lean_socket_address_to_sockaddr_storage(b_obj_arg ip_addr, struct sockaddr_storage* out);

lean_obj_res lean_phys_addr_to_mac_addr(char phys_addr[6]);
lean_obj_res lean_in_addr_to_ipv4_addr(const struct in_addr* ipv4_addr);
lean_obj_res lean_in6_addr_to_ipv6_addr(const struct in6_addr* ipv6_addr);
lean_obj_res lean_in_addr_storage_to_ip_addr(short family, in_addr_storage* ip_addr);
lean_obj_res lean_sockaddr_to_socketaddress(const struct sockaddr* sockaddr);

#endif

extern "C" LEAN_EXPORT lean_obj_res lean_uv_pton_v4(b_obj_arg str_obj);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ntop_v4(b_obj_arg ipv4_addr);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_pton_v6(b_obj_arg str_obj);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ntop_v6(b_obj_arg ipv6_addr);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_interface_addresses(obj_arg /* w */);


}
