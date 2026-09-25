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

// Drains the OpenSSL error queue and returns a single error message combining up to 10 entries.
lean_object * mk_openssl_error(char const * where);
inline lean_obj_res mk_openssl_io_error(char const * where) { return lean_io_result_mk_error(mk_openssl_error(where)); }

// Rejects a path whose bytes cannot reach the OS, which takes it as a NUL-terminated string and so
// would silently act on a prefix. Returns `nullptr` when the path is fine to pass on.
lean_obj_res reject_embedded_nul(b_obj_arg path);

// Reports a failure with no errno behind it, discarding the queue so it cannot taint a later one.
lean_obj_res mk_ssl_invalid_argument(char const * msg);

#endif

}
