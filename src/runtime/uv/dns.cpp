/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues, Henrik Böving
*/
#include "runtime/uv/dns.h"
#include "runtime/uv/util.h"
#include <cstring>
#include <memory>
#include <new>

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {
#ifndef LEAN_EMSCRIPTEN

using namespace std;

bool is_safe_ascii_str(const char *s, size_t len) {
    while (len > 0) {
        char c = *s++;
        if (!((c >= 'a' && c <= 'z') ||
              (c >= 'A' && c <= 'Z') ||
              (c >= '0' && c <= '9') ||
              c == '-' || c == '_' || c == '.' ||
              c == ':' || c == '/' || c == '+' ||
              c == '~' || c == '@' || c == '=' ||
              c == ',' || c == '%'))
            return false;
        len--;
    }
    return true;
}

// A DNS request and the promise its callback settles. The callback deletes it, and so does a failed
// submit. libuv copies the host, service, hints and address it is given.
template<class Req>
struct dns_req_t {
    Req       uv;
    owned_ref promise;
};

using getaddrinfo_req_t = dns_req_t<uv_getaddrinfo_t>;
using getnameinfo_req_t = dns_req_t<uv_getnameinfo_t>;

// Std.Internal.IO.Async.DNS.getAddrInfo (host service : @& String) (family : UInt8) : IO (IO.Promise (Except IO.Error (Array IPAddr)))
extern "C" LEAN_EXPORT lean_obj_res lean_uv_dns_get_info(b_obj_arg name, b_obj_arg service, uint8_t family) {
    char const * name_cstr = lean_string_cstr(name);
    char const * service_cstr = lean_string_cstr(service);

    if (!is_safe_ascii_str(name_cstr, lean_string_size(name) - 1)) {
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("name is not ASCII")));
    }

    if (!is_safe_ascii_str(service_cstr, lean_string_size(service) - 1)) {
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("service is not ASCII")));
    }

    getaddrinfo_req_t * req = new (std::nothrow) getaddrinfo_req_t;
    if (req == nullptr) {
        return io_result_mk_enomem();
    }
    req->uv.data = req;
    req->promise = owned_ref(mk_mt_promise());
    owned_ref promise = owned_ref::retain(req->promise.get());

    struct addrinfo hints;
    memset(&hints, 0, sizeof(hints));

    // Just to avoid changes in enum values changes between platforms.

    switch (family) {
        case 0: hints.ai_family = PF_UNSPEC; break;
        case 1: hints.ai_family = PF_INET; break;
        case 2: hints.ai_family = PF_INET6; break;
        default: hints.ai_family = PF_UNSPEC; break;
    }

    auto on_resolved = [](uv_getaddrinfo_t * uv, int status, struct addrinfo* res) {
        std::unique_ptr<getaddrinfo_req_t> req(static_cast<getaddrinfo_req_t*>(uv->data));

        if (status != 0) {
            resolve_with_code(status, req->promise.get());
            return;
        }

        std::unique_ptr<addrinfo, decltype(&uv_freeaddrinfo)> owned_res(res, uv_freeaddrinfo);
        lean_object * arr = lean_alloc_array(0, 1);

        for (struct addrinfo* ai = res; ai != NULL; ai = ai->ai_next) {
            const struct sockaddr* sin_addr = (const struct sockaddr*)ai->ai_addr;

            in_addr_storage* storage_addr;

            if (sin_addr->sa_family == AF_INET) {
                struct sockaddr_in* ipv4 = (struct sockaddr_in*)sin_addr;
                storage_addr = (in_addr_storage*)&(ipv4->sin_addr);
            } else if (sin_addr->sa_family == AF_INET6) {
                struct sockaddr_in6* ipv6 = (struct sockaddr_in6*)sin_addr;
                storage_addr = (in_addr_storage*)&(ipv6->sin6_addr);
            } else {
                continue;
            }

            lean_object* addr = lean_in_addr_storage_to_ip_addr((short)sin_addr->sa_family, storage_addr);
            arr = lean_array_push(arr, addr);
        }

        lean_promise_resolve(mk_except_ok(arr), req->promise.get());
    };

    int result;

    {
        event_loop_guard guard;
        result = uv_getaddrinfo(global_ev.m_loop, &req->uv, on_resolved, name_cstr, service_cstr, &hints);
    }

    if (result != 0) {
        delete req;
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(promise.release());
}

// Std.Internal.IO.Async.DNS.getNameInfo (host : @& SocketAddress) : IO (IO.Promise (Except IO.Error (String × String)))
extern "C" LEAN_EXPORT lean_obj_res lean_uv_dns_get_name(b_obj_arg addr) {
    getnameinfo_req_t * req = new (std::nothrow) getnameinfo_req_t;
    if (req == nullptr) {
        return io_result_mk_enomem();
    }
    req->uv.data = req;
    req->promise = owned_ref(mk_mt_promise());
    owned_ref promise = owned_ref::retain(req->promise.get());

    sockaddr_storage addr_ptr;
    lean_socket_address_to_sockaddr_storage(addr, &addr_ptr);

    auto on_resolved = [](uv_getnameinfo_t * uv, int status, const char * hostname, const char * service) {
        std::unique_ptr<getnameinfo_req_t> req(static_cast<getnameinfo_req_t*>(uv->data));

        if (status != 0) {
            resolve_with_code(status, req->promise.get());
            return;
        }

        lean_object * r = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(r, 0, lean_mk_string(hostname));
        lean_ctor_set(r, 1, lean_mk_string(service));

        lean_promise_resolve(mk_except_ok(r), req->promise.get());
    };

    int result;
    {
        event_loop_guard guard;
        result = uv_getnameinfo(global_ev.m_loop, &req->uv, on_resolved, (const struct sockaddr*)&addr_ptr, 0);
    }

    if (result != 0) {
        delete req;
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(promise.release());
}

#else

// Std.Internal.IO.Async.DNS.getAddrInfo (host service : @& String) (family : UInt8) : IO (IO.Promise (Except IO.Error (Array IPAddr)))
extern "C" LEAN_EXPORT lean_obj_res lean_uv_dns_get_info(b_obj_arg name, b_obj_arg service, uint8_t family) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.IO.Async.DNS.getNameInfo (host : @& SocketAddress) : IO (IO.Promise (Except IO.Error (String × String)))
extern "C" LEAN_EXPORT lean_obj_res lean_uv_dns_get_name(b_obj_arg ip_addr) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

#endif
}
