/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>

namespace lean {
#ifndef LEAN_EMSCRIPTEN
// Initializes OpenSSL on first call, returning whether the library is usable. Deliberately lazy: a
// program that never opens a TLS connection never loads OpenSSL's providers. Every entry point that
// touches OpenSSL must call this first.
bool ensure_openssl_initialized();

// A `std::unique_ptr` deleter calling `release`.
template<auto release> struct released_by { void operator()(auto * p) const { release(p); } };
#endif
}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg);
extern "C" LEAN_EXPORT lean_obj_res lean_openssl_linked_version(lean_obj_arg);
