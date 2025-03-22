/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Henrik Böving
*/

#include "runtime/uv/net_addr.h"
#include <cstring>

namespace lean {

#ifndef LEAN_EMSCRIPTEN

void lean_ipv4_addr_to_in_addr(b_obj_arg ipv4_addr, in_addr* out) {
    out->s_addr = 0;
    for (int i = 0; i < 4; i++) {
        uint32_t octet = (uint32_t)(uint8_t)lean_unbox(array_uget(ipv4_addr, i));
        out->s_addr |= octet << (3 - i) * 8;
    }
    out->s_addr = htonl(out->s_addr);
}

void lean_ipv6_addr_to_in6_addr(b_obj_arg ipv6_addr, in6_addr* out) {
    for (int i = 0; i < 8; i++) {
        uint16_t segment = htons((uint16_t)lean_unbox(array_uget(ipv6_addr, i)));
        out->s6_addr[2 * i] = (uint8_t)segment;
        out->s6_addr[2 * i + 1] = (uint8_t)(segment >> 8);
    }
}

void lean_socket_address_to_sockaddr_storage(b_obj_arg ip_addr, sockaddr_storage* out) {
    memset(out, 0, sizeof(*out));

    lean_object* socket_addr_obj = lean_ctor_get(ip_addr, 0);
    lean_object* ip_addr_obj = lean_ctor_get(socket_addr_obj, 0);
    uint16_t port_obj = lean_ctor_get_uint16(socket_addr_obj, sizeof(void*)*1);

    if (lean_ptr_tag(ip_addr) == 0) {
        sockaddr_in* cast = (sockaddr_in*)out;
        lean_ipv4_addr_to_in_addr(ip_addr_obj, &cast->sin_addr);
        cast->sin_family = AF_INET;
#ifdef SIN6_LEN
        cast->sin_len = sizeof(*cast);
#endif
        cast->sin_port = htons(port_obj);
    } else {
        sockaddr_in6* cast = (sockaddr_in6*)out;
        lean_ipv6_addr_to_in6_addr(ip_addr_obj, (in6_addr*)&cast->sin6_addr);
        cast->sin6_family = AF_INET6;
#ifdef SIN6_LEN
        cast->sin6_len = sizeof(*cast);
#endif
        cast->sin6_port = htons(port_obj);
    }
}

lean_obj_res lean_in_addr_to_ipv4_addr(const in_addr* ipv4_addr) {
    obj_res ret = alloc_array(0, 4);
    uint32_t hostaddr = ntohl(ipv4_addr->s_addr);

    for (int i = 0; i < 4; i++) {
        uint8_t octet = (uint8_t)(hostaddr >> (3 - i) * 8);
        array_push(ret, lean_box(octet));
    }

    lean_assert(array_size(ret) == 4);
    return ret;
}

lean_obj_res lean_in6_addr_to_ipv6_addr(const in6_addr* ipv6_addr) {
    obj_res ret = alloc_array(0, 8);

    for (int i = 0; i < 16; i += 2) {
        uint16_t part1 = (uint16_t)ipv6_addr->s6_addr[i];
        uint16_t part2 = (uint16_t)ipv6_addr->s6_addr[i + 1];
        uint16_t segment = ntohs((part2 << 8) | part1);
        array_push(ret, lean_box(segment));
    }

    lean_assert(array_size(ret) == 8);
    return ret;
}

lean_obj_res lean_phys_addr_to_mac_addr(char phys_addr[6]) {
    obj_res ret = alloc_array(0, 6);

    for (int i = 0; i < 6; i++) {
        uint8_t byte = (uint8_t)phys_addr[i];
        array_push(ret, lean_box(byte));
    }

    lean_assert(array_size(ret) == 6);
    return ret;
}

lean_obj_res lean_mk_socketaddress(lean_obj_res ip_addr, uint16_t port) {
    lean_obj_res socket_addr = lean_alloc_ctor(0, 1, 2);
    lean_ctor_set(socket_addr, 0, ip_addr);
    lean_ctor_set_uint16(socket_addr, sizeof(void*)*1, port);
    return socket_addr;
}

lean_obj_res lean_in_addr_storage_to_ip_addr(short family, in_addr_storage* ip_addr) {
    lean_object* part;

    if (family == AF_INET) {
        part = lean_in_addr_to_ipv4_addr(&ip_addr->ipv4);
    } else if (family == AF_INET6) {
        part = lean_in6_addr_to_ipv6_addr(&ip_addr->ipv6);
    } else {
        lean_unreachable();
    }

    lean_object* ctor = lean_alloc_ctor(family == AF_INET6 ? 1 : 0, 1, 0);
    lean_ctor_set(ctor, 0, part);

    return ctor;
}

lean_obj_res lean_sockaddr_to_socketaddress(const struct sockaddr* sockaddr) {
    lean_object* part = nullptr;
    int tag;

    if (sockaddr->sa_family == AF_INET) {
        const struct sockaddr_in* addr_in = (const struct sockaddr_in*)sockaddr;
        const in_addr* ipv4_addr = &addr_in->sin_addr;
        lean_obj_res lean_ipv4 = lean_in_addr_to_ipv4_addr(ipv4_addr);
        uint16_t port = ntohs(addr_in->sin_port);
        part = lean_mk_socketaddress(lean_ipv4, port);
        tag = 0;
    } else if (sockaddr->sa_family == AF_INET6) {
        const struct sockaddr_in6* addr_in6 = (const struct sockaddr_in6*)sockaddr;
        const in6_addr* ipv6_addr = &addr_in6->sin6_addr;
        lean_obj_res lean_ipv6 = lean_in6_addr_to_ipv6_addr(ipv6_addr);
        uint16_t port = ntohs(addr_in6->sin6_port);
        part = lean_mk_socketaddress(lean_ipv6, port);
        tag = 1;
    } else {
         lean_unreachable();
    }

    lean_object* ctor = lean_alloc_ctor(tag, 1, 0);
    lean_ctor_set(ctor, 0, part);

    return ctor;
}


/* Std.Net.IPV4Addr.ofString (s : @&String) : Option IPV4Addr */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_pton_v4(b_obj_arg str_obj) {
    const char* str = string_cstr(str_obj);
    in_addr internal;
    if (uv_inet_pton(AF_INET, str, &internal) == 0) {
        return mk_option_some(lean_in_addr_to_ipv4_addr(&internal));
    } else {
        return mk_option_none();
    }
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
    in6_addr internal;
    if (uv_inet_pton(AF_INET6, str, &internal) == 0) {
        return mk_option_some(lean_in6_addr_to_ipv6_addr(&internal));
    } else {
        return mk_option_none();
    }
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
extern "C" LEAN_EXPORT lean_obj_res lean_uv_interface_addresses(obj_arg /* w */) {
    uv_interface_address_t* info;
    int count;

    if (uv_interface_addresses(&info, &count) != 0) {
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to get interface addresses")));
    }

    lean_object *arr = lean_alloc_array(0, count);

    for (int i = 0; i < count; i++) {
        uv_interface_address_t interface = info[i];

        int sin_family = interface.address.address4.sin_family;
        in_addr_storage* socket_address;
        in_addr_storage* netmask_address;

        if (sin_family == AF_INET) {
            socket_address = (in_addr_storage*)&interface.address.address4.sin_addr;
            netmask_address =(in_addr_storage*) &interface.netmask.netmask4.sin_addr;
        } else if (sin_family == AF_INET6) {
            socket_address = (in_addr_storage*)&interface.address.address6.sin6_addr;
            netmask_address = (in_addr_storage*)&interface.netmask.netmask6.sin6_addr;
        } else {
            continue;
        }

        lean_object *iface = lean_alloc_ctor(0, 4, 1);
        lean_ctor_set(iface, 0, lean_mk_string(interface.name));
        lean_ctor_set(iface, 1, lean_phys_addr_to_mac_addr(interface.phys_addr));
        lean_ctor_set_uint8(iface, sizeof(void*)*4, interface.is_internal);

        lean_ctor_set(iface, 2, lean_in_addr_storage_to_ip_addr(sin_family, socket_address));
        lean_ctor_set(iface, 3, lean_in_addr_storage_to_ip_addr(sin_family, netmask_address));

        arr = lean_array_push(arr, iface);
    }

    uv_free_interface_addresses(info, count);

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
extern "C" LEAN_EXPORT lean_obj_res lean_uv_interface_addresses(obj_arg /* w */) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

#endif
}
