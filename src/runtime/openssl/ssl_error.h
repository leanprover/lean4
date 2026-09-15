/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#pragma once

#include <lean/lean.h>
#include "runtime/io.h"
#include "runtime/object.h"

#ifndef LEAN_EMSCRIPTEN
#include <openssl/ssl.h>
#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

// PEM material the caller named: a path when `is_file`, otherwise the bytes themselves.
struct pem_source {
    b_obj_arg obj;
    bool is_file;

    char const * data() const { return lean_string_cstr(obj); }
    size_t size() const { return lean_string_size(obj) - 1; }
};

// Drains the OpenSSL error queue and returns a single error message combining up to 10 entries.
lean_object * mk_openssl_error(char const * where);
inline lean_obj_res mk_openssl_io_error(char const * where) { return lean_io_result_mk_error(mk_openssl_error(where)); }

// Rejects a path whose bytes cannot reach the OS, which takes it as a NUL-terminated string and so
// would silently act on a prefix. Returns `nullptr` when the path is fine to pass on.
lean_obj_res reject_embedded_nul(b_obj_arg path);

// Reports a failure with no errno behind it, discarding the queue so it cannot taint a later one.
lean_obj_res mk_ssl_invalid_argument(char const * msg);

// Reports a failure against a path. `errnum` is the `errno` the open failed with, or 0 for a
// failure with no OS error behind it (unparsable PEM, a key that does not match its certificate).
lean_obj_res mk_ssl_file_error(b_obj_arg file, char const * msg, int errnum = 0);

// Reports a failure against PEM material, naming the path when there is one to name.
lean_obj_res mk_pem_error(pem_source src, char const * msg, int errnum = 0);

// Whether a certificate was turned away on policy grounds rather than being unreadable as PEM.
bool rejected_by_security_level();

#endif

}
