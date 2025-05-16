/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues, Henrik Böving
*/
#include "runtime/uv/dns.h"
#include <cstring>

namespace lean {
#ifndef LEAN_EMSCRIPTEN

using namespace std;

// Std.Internal.IO.Async.DNS.getAddrInfo (host service : @& String) : IO (IO.Promise (Except IO.Error (Array SocketAddress)))
extern "C" LEAN_EXPORT lean_obj_res lean_uv_dns_get_info(b_obj_arg name, b_obj_arg service, obj_arg /* w */) {
    lean_object* promise = lean_promise_new();
    mark_mt(promise);

    uv_getaddrinfo_t* resolver = (uv_getaddrinfo_t*)malloc(sizeof(uv_getaddrinfo_t));
    resolver->data = promise;

    char const * name_cstr = lean_string_cstr(name);
    char const * service_cstr = lean_string_cstr(service);

    struct addrinfo hints;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = PF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;

    event_loop_lock(&global_ev);

    lean_inc(promise);

    int result = uv_getaddrinfo(global_ev.loop, resolver, [](uv_getaddrinfo_t* req, int status, struct addrinfo* res) {
        lean_object* promise = (lean_object*) req->data;

        if (status != 0) {
            lean_promise_resolve_with_code(status, promise);
            return;
        }

        lean_object *arr = lean_alloc_array(0, 1);

        for (struct addrinfo* ai = res; ai != NULL; ai = ai->ai_next) {
            const struct sockaddr* sin_addr = (const struct sockaddr*)ai->ai_addr;
            lean_object* addr = lean_sockaddr_to_socketaddress(sin_addr);
            arr = lean_array_push(arr, addr);
        }

        lean_promise_resolve(mk_except_ok(arr), promise);

        uv_freeaddrinfo(res);
        lean_dec(promise);
        free(req);
    }, name_cstr, service_cstr, &hints);

    if (result != 0) {
        lean_dec(promise); // The structure does not own it.
        lean_dec(promise); // We are not going to return it.

        free(resolver);

        event_loop_unlock(&global_ev);

        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    event_loop_unlock(&global_ev);
    return lean_io_result_mk_ok(promise);
}

// Std.Internal.IO.Async.DNS.getNameInfo (host : @& SocketAddress) : IO (IO.Promise (Except IO.Error (String × String)))
extern "C" LEAN_EXPORT lean_obj_res lean_uv_dns_get_name(b_obj_arg addr, obj_arg /* w */) {
    lean_object* promise = lean_promise_new();
    mark_mt(promise);

    uv_getnameinfo_t* req = (uv_getnameinfo_t*)malloc(sizeof(uv_getnameinfo_t));
    req->data = promise;

    sockaddr_storage addr_ptr;
    lean_socket_address_to_sockaddr_storage(addr, &addr_ptr);

    event_loop_lock(&global_ev);
    lean_inc(promise);

    int result = uv_getnameinfo(global_ev.loop, req, [](uv_getnameinfo_t* req, int status, const char* hostname, const char* service) {
        lean_object* promise = (lean_object*) req->data;

        lean_object * r = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(r, 0, lean_mk_string(hostname));
        lean_ctor_set(r, 1, lean_mk_string(service));

        if (status != 0) {
            lean_promise_resolve_with_code(status, promise);
            return;
        }

        lean_promise_resolve(mk_except_ok(r), promise);

        lean_dec(promise);
        free(req);
    }, (const struct sockaddr*)&addr_ptr, 0);

    if (result != 0) {
        lean_dec(promise); // The structure does not own it.
        lean_dec(promise); // We are not going to return it.

        free(req);

        event_loop_unlock(&global_ev);

        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    event_loop_unlock(&global_ev);
    return lean_io_result_mk_ok(promise);
}

#else

// Std.Internal.IO.Async.DNS.getAddrInfo (host service : @& String) : IO (IO.Promise (Except IO.Error (Array SocketAddress)))
extern "C" LEAN_EXPORT lean_obj_res lean_uv_dns_get_info(b_obj_arg name, uint16_t service, obj_arg /* w */) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.IO.Async.DNS.getNameInfo (host : @& SocketAddress) : IO (IO.Promise (Except IO.Error (String × String)))
extern "C" LEAN_EXPORT lean_obj_res lean_uv_dns_get_name(b_obj_arg ip_addr, obj_arg /* w */) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

#endif
}
