/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Henrik Böving
*/

#include "runtime/uv/net_addr.h"
#include "runtime/uv/util.h"
#include <cstring>

namespace lean {

#ifndef LEAN_EMSCRIPTEN

// In network byte order the bytes of `s_addr` are the octets of an `IPv4Addr`, and each pair of bytes
// of `s6_addr` is one big-endian segment of an `IPv6Addr`.

void lean_ipv4_addr_to_in_addr(b_obj_arg ipv4_addr, in_addr* out) {
    uint8_t * bytes = (uint8_t*)&out->s_addr;
    for (int i = 0; i < 4; i++) {
        bytes[i] = (uint8_t)lean_unbox(array_uget(ipv4_addr, i));
    }
}

void lean_ipv6_addr_to_in6_addr(b_obj_arg ipv6_addr, in6_addr* out) {
    for (int i = 0; i < 8; i++) {
        uint16_t segment = (uint16_t)lean_unbox(array_uget(ipv6_addr, i));
        out->s6_addr[2 * i] = (uint8_t)(segment >> 8);
        out->s6_addr[2 * i + 1] = (uint8_t)segment;
    }
}

void lean_ip_addr_to_in_addr_storage(b_obj_arg ip_addr, int* type, in_addr_storage* out) {
    lean_object* ip_obj = lean_ctor_get(ip_addr, 0);

    if (lean_ptr_tag(ip_addr) == 0) {
        lean_ipv4_addr_to_in_addr(ip_obj, &out->ipv4);
        *type = AF_INET;
    } else {
        lean_ipv6_addr_to_in6_addr(ip_obj, &out->ipv6);
        *type = AF_INET6;
    }
}

void lean_ip_addr_ntop(b_obj_arg ip_addr, char *buffer, size_t buffer_size) {
    int ip_type;
    in_addr_storage ip_addr_storage;

    lean_ip_addr_to_in_addr_storage(ip_addr, &ip_type, &ip_addr_storage);
    int ret = uv_inet_ntop(ip_type, &ip_addr_storage, buffer, buffer_size);

    lean_always_assert(ret == 0);
}

void lean_socket_address_to_sockaddr_storage(b_obj_arg socket_addr, sockaddr_storage * out) {
    memset(out, 0, sizeof(*out));

    // `SocketAddress.v4`/`.v6` wraps a `{ addr, port }` structure.
    lean_object * versioned = lean_ctor_get(socket_addr, 0);
    lean_object * ip_addr = lean_ctor_get(versioned, 0);
    uint16_t port = lean_ctor_get_uint16(versioned, sizeof(void*)*1);

    if (lean_ptr_tag(socket_addr) == 0) {
        sockaddr_in * sin = (sockaddr_in*)out;
        lean_ipv4_addr_to_in_addr(ip_addr, &sin->sin_addr);
        sin->sin_family = AF_INET;
#ifdef SIN6_LEN
        sin->sin_len = sizeof(*sin);
#endif
        sin->sin_port = htons(port);
    } else {
        sockaddr_in6 * sin6 = (sockaddr_in6*)out;
        lean_ipv6_addr_to_in6_addr(ip_addr, &sin6->sin6_addr);
        sin6->sin6_family = AF_INET6;
#ifdef SIN6_LEN
        sin6->sin6_len = sizeof(*sin6);
#endif
        sin6->sin6_port = htons(port);
    }
}

lean_obj_res lean_in_addr_to_ipv4_addr(const in_addr* ipv4_addr) {
    const uint8_t * bytes = (const uint8_t*)&ipv4_addr->s_addr;
    lean_object * ret = lean_alloc_array(4, 4);
    for (int i = 0; i < 4; i++) {
        lean_array_set_core(ret, i, lean_box(bytes[i]));
    }
    return ret;
}

lean_obj_res lean_in6_addr_to_ipv6_addr(const in6_addr* ipv6_addr) {
    lean_object * ret = lean_alloc_array(8, 8);
    for (int i = 0; i < 8; i++) {
        uint16_t segment = (uint16_t)((ipv6_addr->s6_addr[2 * i] << 8) | ipv6_addr->s6_addr[2 * i + 1]);
        lean_array_set_core(ret, i, lean_box(segment));
    }
    return ret;
}

lean_obj_res lean_phys_addr_to_mac_addr(const char phys_addr[6]) {
    lean_object * ret = lean_alloc_array(6, 6);
    for (int i = 0; i < 6; i++) {
        lean_array_set_core(ret, i, lean_box((uint8_t)phys_addr[i]));
    }
    return ret;
}

static lean_obj_res lean_mk_socketaddress(lean_obj_arg ip_addr, uint16_t port) {
    lean_obj_res socket_addr = lean_alloc_ctor(0, 1, 2);
    lean_ctor_set(socket_addr, 0, ip_addr);
    lean_ctor_set_uint16(socket_addr, sizeof(void*)*1, port);
    return socket_addr;
}

lean_obj_res lean_in_addr_to_ip_addr(int family, const void * addr) {
    lean_object* part;

    if (family == AF_INET) {
        part = lean_in_addr_to_ipv4_addr(static_cast<const in_addr*>(addr));
    } else if (family == AF_INET6) {
        part = lean_in6_addr_to_ipv6_addr(static_cast<const in6_addr*>(addr));
    } else {
        lean_unreachable();
    }

    lean_object* ctor = lean_alloc_ctor(family == AF_INET6 ? 1 : 0, 1, 0);
    lean_ctor_set(ctor, 0, part);
    return ctor;
}

lean_obj_res lean_sockaddr_to_socketaddress(const sockaddr * sa) {
    lean_object * ip_addr;
    uint16_t port;
    unsigned tag;

    if (sa->sa_family == AF_INET) {
        const sockaddr_in * sin = (const sockaddr_in*)sa;
        ip_addr = lean_in_addr_to_ipv4_addr(&sin->sin_addr);
        port = ntohs(sin->sin_port);
        tag = 0;
    } else if (sa->sa_family == AF_INET6) {
        const sockaddr_in6 * sin6 = (const sockaddr_in6*)sa;
        ip_addr = lean_in6_addr_to_ipv6_addr(&sin6->sin6_addr);
        port = ntohs(sin6->sin6_port);
        tag = 1;
    } else {
        lean_unreachable();
    }

    lean_object* ctor = lean_alloc_ctor(tag, 1, 0);
    lean_ctor_set(ctor, 0, lean_mk_socketaddress(ip_addr, port));
    return ctor;
}

/* Std.Net.IPV4Addr.ofString (s : @&String) : Option IPV4Addr */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_pton_v4(b_obj_arg str_obj) {
    const char* str = string_cstr(str_obj);
    if (strlen(str) != lean_string_size(str_obj) - 1) {
       return mk_option_none();
    }
    in_addr internal;
    if (uv_inet_pton(AF_INET, str, &internal) != 0) {
        return mk_option_none();
    }
    return mk_option_some(lean_in_addr_to_ipv4_addr(&internal));
}

/* Std.Net.IPV4Addr.toString (addr : @&IPV4Addr) : String */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ntop_v4(b_obj_arg ipv4_addr) {
    in_addr internal;
    lean_ipv4_addr_to_in_addr(ipv4_addr, &internal);
    char dst[INET_ADDRSTRLEN];
    int ret = uv_inet_ntop(AF_INET, &internal, dst, sizeof(dst));
    lean_always_assert(ret == 0);
    return lean_mk_string(dst);
}

/* Std.Net.IPV6Addr.ofString (s : @&String) : Option IPV6Addr */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_pton_v6(b_obj_arg str_obj) {
    const char* str = string_cstr(str_obj);
    // libuv drops a `%` zone suffix without checking it, and `IPv6Addr` has no zone to keep it in.
    if (strlen(str) != lean_string_size(str_obj) - 1 || strchr(str, '%') != nullptr) {
       return mk_option_none();
    }
    in6_addr internal;
    if (uv_inet_pton(AF_INET6, str, &internal) != 0) {
        return mk_option_none();
    }
    return mk_option_some(lean_in6_addr_to_ipv6_addr(&internal));
}

/* Std.Net.IPV6Addr.toString (addr : @&IPV6Addr) : String */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ntop_v6(b_obj_arg ipv6_addr) {
    in6_addr internal;
    lean_ipv6_addr_to_in6_addr(ipv6_addr, &internal);
    char dst[INET6_ADDRSTRLEN];
    int ret = uv_inet_ntop(AF_INET6, &internal, dst, sizeof(dst));
    lean_always_assert(ret == 0);
    return lean_mk_string(dst);
}

/* Std.Net.networkInterface : IO (Array InterfaceAddress) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_interface_addresses() {
    uv_interface_address_t * infos;
    int count;

    if (uv_interface_addresses(&infos, &count) != 0) {
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to get interface addresses")));
    }
    uv_owned_array<uv_interface_address_t, uv_free_interface_addresses> interfaces(infos, count);

    lean_object *arr = lean_alloc_array(0, count);

    for (uv_interface_address_t const & info : interfaces) {
        int family = info.address.address4.sin_family;
        const void * address;
        const void * netmask;

        if (family == AF_INET) {
            address = &info.address.address4.sin_addr;
            netmask = &info.netmask.netmask4.sin_addr;
        } else if (family == AF_INET6) {
            address = &info.address.address6.sin6_addr;
            netmask = &info.netmask.netmask6.sin6_addr;
        } else {
            continue;
        }

        lean_object *iface = lean_alloc_ctor(0, 4, 1);
        lean_ctor_set(iface, 0, lean_mk_string(info.name));
        lean_ctor_set(iface, 1, lean_phys_addr_to_mac_addr(info.phys_addr));
        lean_ctor_set(iface, 2, lean_in_addr_to_ip_addr(family, address));
        lean_ctor_set(iface, 3, lean_in_addr_to_ip_addr(family, netmask));
        lean_ctor_set_uint8(iface, sizeof(void*)*4, info.is_internal);

        arr = lean_array_push(arr, iface);
    }

    return lean_io_result_mk_ok(arr);
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

/* Std.Net.networkInterface : IO (Array InterfaceAddress) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_interface_addresses() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

#endif
}
