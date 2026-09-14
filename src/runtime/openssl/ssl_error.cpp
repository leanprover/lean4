/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/ssl_error.h"

#ifndef LEAN_EMSCRIPTEN

#include <openssl/err.h>
#include <cerrno>
#include <cstring>
#include <string>
#include <sys/stat.h>

#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

lean_object * mk_openssl_error(char const * where) {
    std::string msg(where);

    for (int i = 0; i < 10; i++) {
        unsigned long err = ERR_get_error();
        if (err == 0) break;

        char err_buf[256];
        ERR_error_string_n(err, err_buf, sizeof(err_buf));

        msg += i == 0 ? ": " : "; ";
        msg += err_buf;
    }

    if (ERR_peek_error() != 0) {
        msg += "; ... (truncated)";
        ERR_clear_error();
    }

    return lean_mk_io_user_error(mk_string(msg));
}

lean_obj_res reject_embedded_nul(b_obj_arg path) {
    return strlen(lean_string_cstr(path)) == lean_string_size(path) - 1
        ? nullptr
        : mk_embedded_nul_error(path);
}

lean_obj_res mk_ssl_invalid_argument(char const * msg) {
    ERR_clear_error();
    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string(msg)));
}

lean_obj_res mk_ssl_file_error(b_obj_arg file, char const * msg, int errnum) {
    ERR_clear_error();

    struct stat st;

    if (stat(lean_string_cstr(file), &st) == 0 && !S_ISREG(st.st_mode)) {
        lean_inc(file);
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument_file(
            file, EINVAL, mk_string(std::string(msg) + " (the path is not a regular file)")));
    }

    if (errnum != 0) return lean_io_result_mk_error(decode_io_error(errnum, file));

    lean_inc(file);
    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument_file(
        file, EINVAL, mk_string(msg)));
}

lean_obj_res mk_pem_error(pem_source src, char const * msg, int errnum) {
    return src.is_file ? mk_ssl_file_error(src.obj, msg, errnum) : mk_ssl_invalid_argument(msg);
}

bool rejected_by_security_level() {
    unsigned long err = ERR_peek_last_error();

    if (ERR_GET_LIB(err) != ERR_LIB_SSL) return false;

    int reason = ERR_GET_REASON(err);
    return reason == SSL_R_EE_KEY_TOO_SMALL || reason == SSL_R_CA_KEY_TOO_SMALL ||
           reason == SSL_R_CA_MD_TOO_WEAK;
}

#endif

}
