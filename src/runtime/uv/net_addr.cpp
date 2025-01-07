/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Henrik Böving
*/

#include "runtime/uv/net_addr.h"
#include <cstring>

namespace lean {

/*
 * TODO:
 * - implement conversions
 */

#ifndef LEAN_EMSCRIPTEN

void lean_ipv4_addr_to_in_addr(b_obj_arg ipv4_addr, struct in_addr* out) {
    uint8_t ipv4_addr_array[4];
    for (int i = 0; i < 4; i++) {
        ipv4_addr_array[i] = (uint8_t)lean_unbox(array_uget(ipv4_addr, i));
    }
    memcpy(&out->s_addr, ipv4_addr_array, 4);
    out->s_addr = htonl(out->s_addr);
}

void lean_ipv6_addr_to_in6_addr(b_obj_arg ipv6_addr, struct in6_addr* out) {
    uint16_t ipv6_addr_array[8];
    for (int i = 0; i < 8; i++) {
        ipv6_addr_array[i] = htons((uint16_t)lean_unbox(array_uget(ipv6_addr, i)));
    }
    memcpy(&out->s6_addr, ipv6_addr_array, 16);
}

lean_obj_res lean_in_addr_to_ipv4_addr(const struct in_addr* ipv4_addr) {

}

lean_obj_res lean_in6_addr_to_ipv6_addr(const struct in6_addr* ipv6_addr) {

}

/* Std.Net.IPV4Addr.ofString (s : @&String) : Option IPV4Addr */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_pton_v4(b_obj_arg str_obj) {
    const char* str = string_cstr(str_obj);
    struct in_addr internal;
    if (uv_inet_pton(AF_INET, str, &internal) == 0) {
        return mk_option_some(lean_in_addr_to_ipv4_addr(&internal));
    } else {
        return mk_option_none();
    }
}

/* Std.Net.IPV4Addr.toString (addr : @&IPV4Addr) : String */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ntop_v4(b_obj_arg ipv4_addr) {
    struct in_addr internal;
    lean_ipv4_addr_to_in_addr(ipv4_addr, &internal);
    char dst[INET_ADDRSTRLEN];
    int ret = uv_inet_ntop(AF_INET, &internal, dst, sizeof(dst));
    lean_always_assert(ret == 0);
    return lean_mk_string(dst);
}

/* Std.Net.IPV6Addr.ofString (s : @&String) : Option IPV6Addr */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_pton_v6(b_obj_arg str_obj) {
    const char* str = string_cstr(str_obj);
    struct in6_addr internal;
    if (uv_inet_pton(AF_INET6, str, &internal) == 0) {
        return mk_option_some(lean_in6_addr_to_ipv6_addr(&internal));
    } else {
        return mk_option_none();
    }
}

/* Std.Net.IPV6Addr.toString (addr : @&IPV6Addr) : String */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ntop_v6(b_obj_arg ipv6_addr) {
    struct in6_addr internal;
    lean_ipv6_addr_to_in6_addr(ipv6_addr, &internal);
    char dst[INET6_ADDRSTRLEN];
    int ret = uv_inet_ntop(AF_INET6, &internal, dst, sizeof(dst));
    lean_always_assert(ret == 0);
    return lean_mk_string(dst);
}

#else

/* Std.Net.IPV4Addr.ofString (s : @&String) : Option IPV4Addr */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_pton_v4(b_obj_arg str_obj) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

/* Std.Net.IPV4Addr.toString (addr : @&IPV4Addr) : String */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ntop_v4(b_obj_arg ipv4_addr) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

/* Std.Net.IPV6Addr.ofString (s : @&String) : Option IPV6Addr */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_pton_v6(b_obj_arg str_obj) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

/* Std.Net.IPV6Addr.toString (addr : @&IPV6Addr) : String */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ntop_v6(b_obj_arg ipv6_addr) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

#endif
}
