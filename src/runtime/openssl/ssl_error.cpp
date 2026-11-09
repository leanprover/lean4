/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/ssl_error.h"

#ifndef LEAN_EMSCRIPTEN

#include <openssl/err.h>
#include <cerrno>
#include <string>

#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

lean_object * mk_openssl_error(char const * where) {
    std::string msg(where);

    // Only the reason text is kept; the packed code, library and function names mean nothing to a caller.
    bool first = true;
    for (int i = 0; i < 10; i++) {
        unsigned long err = ERR_get_error();
        if (err == 0) break;

        char const * reason = ERR_reason_error_string(err);
        if (reason == nullptr) continue;

        msg += first ? ": " : "; ";
        msg += reason;
        first = false;
    }

    if (ERR_peek_error() != 0) {
        msg += "; ... (truncated)";
        ERR_clear_error();
    }

    return lean_mk_io_user_error(mk_string(msg));
}

lean_obj_res mk_ssl_invalid_argument(char const * msg) {
    ERR_clear_error();
    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string(msg)));
}

#endif

}
