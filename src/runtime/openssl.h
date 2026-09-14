/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>

namespace lean {
void initialize_openssl();
void finalize_openssl();

#ifndef LEAN_EMSCRIPTEN
// Initializes OpenSSL on first call, returning whether the library is usable. Deliberately lazy: a
// program that never opens a TLS connection never loads OpenSSL's providers. Every entry point that
// touches OpenSSL must call this first.
bool ensure_openssl_initialized();
#endif
}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg);
