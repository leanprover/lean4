/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>

#ifndef LEAN_EMSCRIPTEN
#include <openssl/ssl.h>
#endif

namespace lean {

void initialize_openssl();
void finalize_openssl();

#ifndef LEAN_EMSCRIPTEN
SSL_CTX * get_openssl_server_ctx();
SSL_CTX * get_openssl_client_ctx();
#endif

}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg);
