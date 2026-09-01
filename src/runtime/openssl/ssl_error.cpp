/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/ssl_error.h"

#ifndef LEAN_EMSCRIPTEN

#include <uv.h>
#include <openssl/err.h>
#include <openssl/x509.h>
#include <openssl/x509_vfy.h>
#include <cerrno>
#include <cstdio>
#include <cstring>
#include <string>
#include <sys/stat.h>

#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

lean_object* mk_openssl_error(const char* where) {
    std::string msg(where);

    for (int i = 0; i < 10; i++) {
        unsigned long err = ERR_get_error();
        if (err == 0) {
            break;
        }

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

lean_obj_res mk_ssl_protocol_error(const char* msg) {
    return lean_io_result_mk_error(lean_mk_io_error_protocol_error(EPROTO, mk_string(msg)));
}

lean_obj_res reject_embedded_nul(b_obj_arg path) {
    return strlen(lean_string_cstr(path)) == lean_string_size(path) - 1
        ? nullptr
        : mk_embedded_nul_error(path);
}

lean_obj_res mk_ssl_invalid_argument(const char* msg) {
    ERR_clear_error();
    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string(msg)));
}

lean_obj_res mk_ssl_eof_error() {
    return lean_io_result_mk_error(lean_mk_io_error_eof(lean_box(0)));
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

    if (ERR_GET_LIB(err) != ERR_LIB_SSL) {
        return false;
    }

    int reason = ERR_GET_REASON(err);
    return reason == SSL_R_EE_KEY_TOO_SMALL || reason == SSL_R_CA_KEY_TOO_SMALL ||
           reason == SSL_R_CA_MD_TOO_WEAK;
}

void take_ssl_error_reason(int* sys_errno, int* reason) {
    unsigned long err;

    while ((err = ERR_get_error()) != 0) {
        // `ERR_GET_REASON` masks off the library but not the reason flags, which sit inside
        // `ERR_REASON_MASK`, so a code carrying `ERR_RFLAG_COMMON` comes back far above every
        // `SSL_R_*` — and above `SSL_AD_REASON_OFFSET`, where `ssl_reason_message` would read it as
        // a received alert. Those are the library-wide `ERR_R_*` conditions, which libssl raises
        // under its own library for failures of its own (a certificate it cannot parse reaches here
        // as `ERR_R_ASN1_LIB`); none of them names a TLS condition, so they are passed over for the
        // fallback message rather than decoded.
        if (ERR_COMMON_ERROR(err)) {
            continue;
        }

        if (ERR_GET_LIB(err) == ERR_LIB_SYS) {
            if (*sys_errno == 0) {
                *sys_errno = ERR_GET_REASON(err);
            }
        } else if (ERR_GET_LIB(err) == ERR_LIB_SSL && *reason == 0) {
            *reason = ERR_GET_REASON(err);
        }
    }
}

// A received fatal alert is queued as `SSL_AD_REASON_OFFSET` plus the alert descriptor rather than
// as a distinct `SSL_R_*` constant, so the whole range is decoded here instead of being enumerated.
// These are the peer's verdict on us, which no other mapping below covers.
static const char* ssl_alert_message(int reason) {
    switch (reason) {
    case SSL_R_TLSV1_ALERT_UNKNOWN_CA:
        return "the peer rejected our certificate: it does not trust the issuing CA";
    case SSL_R_SSLV3_ALERT_BAD_CERTIFICATE:
    case SSL_R_TLSV1_ALERT_ACCESS_DENIED:
        return "the peer rejected our certificate";
    case SSL_R_SSLV3_ALERT_CERTIFICATE_EXPIRED:
        return "the peer rejected our certificate as expired";
    case SSL_R_SSLV3_ALERT_CERTIFICATE_REVOKED:
        return "the peer rejected our certificate as revoked";
    case SSL_R_SSLV3_ALERT_HANDSHAKE_FAILURE:
        return "the peer could not agree on TLS parameters with us";
    case SSL_R_TLSV1_ALERT_PROTOCOL_VERSION:
        return "the peer does not support the TLS version we offered";
    case SSL_R_TLSV1_ALERT_INTERNAL_ERROR:
        return "the peer reported an internal error";
    case SSL_R_TLSV1_UNRECOGNIZED_NAME:
        return "the peer does not recognize the server name we requested";
    case SSL_R_TLSV13_ALERT_CERTIFICATE_REQUIRED:
        return "the peer requires a client certificate";
    default:
        return "the peer aborted the TLS session with a fatal alert";
    }
}

// The TLS conditions that map to a fixed message; `nullptr` for anything else.
static const char* ssl_reason_message(int reason) {
    if (reason >= SSL_AD_REASON_OFFSET) {
        return ssl_alert_message(reason);
    }

    switch (reason) {
    case SSL_R_APPLICATION_DATA_AFTER_CLOSE_NOTIFY:
        return "application data arrived after the TLS session was closed";
    case SSL_R_DECRYPTION_FAILED_OR_BAD_RECORD_MAC:
        return "a TLS record did not authenticate; the stream was corrupted or tampered with";
    case SSL_R_WRONG_VERSION_NUMBER:
        return "the peer sent a TLS record with an unrecognized version; it may not be speaking TLS";
    case SSL_R_HTTP_REQUEST:
        return "the peer sent a plaintext HTTP request to a TLS server";
    case SSL_R_HTTPS_PROXY_REQUEST:
        return "the peer sent a plaintext HTTPS proxy request to a TLS server";
    case SSL_R_UNSUPPORTED_PROTOCOL:
        return "the peer does not support a compatible TLS version";
    case SSL_R_NO_SHARED_CIPHER:
        return "the peer shares no supported TLS cipher suite";
    default:
        return nullptr;
    }
}

bool ssl_input_truncated(ssl_error_state* st, int reason) {
    if (reason != SSL_R_UNEXPECTED_EOF_WHILE_READING) {
        return false;
    }

    st->input_truncated = true;
    return true;
}

// Reports a syscall failure raised under the BIO, which already carries an errno.
//
// Not `decode_io_error`: it asserts the filename is absent for the errnos a transport failure
// raises and dereferences it for others (`EINTR`, `ENOENT`), and there is no file to name here.
//
// The reason is read as a CRT `errno`, which is what OpenSSL stores on POSIX; on Windows it stores a
// Win32 or Winsock code there instead, which this would misname. Both BIOs are memory-backed, so no
// syscall runs under them and only a stray `ERR_LIB_SYS` entry reaches this at all.
static lean_obj_res mk_ssl_errno_error(int sys_errno) {
    char errbuf[128];
    lean_object* details = mk_string(uv_strerror_r(lean_crt_to_uv_err(sys_errno), errbuf, sizeof(errbuf)));

    switch (sys_errno) {
    case EPIPE: case ECONNRESET: case ENETDOWN:
        return lean_io_result_mk_error(lean_mk_io_error_resource_vanished(sys_errno, details));
    case EPROTO: case EPROTOTYPE: case EPROTONOSUPPORT:
        return lean_io_result_mk_error(lean_mk_io_error_protocol_error(sys_errno, details));
    case ETIMEDOUT:
        return lean_io_result_mk_error(lean_mk_io_error_time_expired(sys_errno, details));
    case ENOMEM: case ENOBUFS:
        return lean_io_result_mk_error(lean_mk_io_error_resource_exhausted(sys_errno, details));
    case EACCES: case EPERM:
        return lean_io_result_mk_error(lean_mk_io_error_permission_denied(sys_errno, details));
    case EINVAL:
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(sys_errno, details));
    default:
        return lean_io_result_mk_error(lean_mk_io_error_other_error(sys_errno, details));
    }
}

lean_obj_res mk_ssl_error_of(SSL* ssl, ssl_error_state* st, int ssl_err, int sys_errno, int reason,
                             const char* fallback) {
    if (reason == SSL_R_PROTOCOL_IS_SHUTDOWN) {
        return mk_ssl_protocol_error("the TLS session was already shut down");
    }

    // Every condition diagnosed below is fatal, and this is the one place they all pass through.
    st->failed = true;

    if (ssl_err == SSL_ERROR_SYSCALL && sys_errno != 0) {
        return mk_ssl_errno_error(sys_errno);
    }

    if (ssl_err == SSL_ERROR_ZERO_RETURN) {
        return lean_io_result_mk_error(lean_mk_io_error_resource_vanished(EPIPE, mk_string("the peer closed the TLS session")));
    }

    if (reason == SSL_R_CERTIFICATE_VERIFY_FAILED) {
        const char* detail = X509_verify_cert_error_string(SSL_get_verify_result(ssl));
        std::string msg("the peer's certificate could not be verified: ");
        msg += detail != nullptr ? detail : "unknown certificate verification error";
        return mk_ssl_protocol_error(msg.c_str());
    }

    if (ssl_input_truncated(st, reason)) {
        return mk_ssl_eof_error();
    }

    const char* msg = ssl_reason_message(reason);

    if (msg != nullptr) {
        return mk_ssl_protocol_error(msg);
    }

    if (ssl_err == SSL_ERROR_SYSCALL) {
        return mk_ssl_protocol_error("the TLS session was aborted by an earlier fatal error");
    }

    return mk_ssl_protocol_error(fallback);
}

lean_obj_res mk_ssl_error(SSL* ssl, ssl_error_state* st, int ssl_err, const char* fallback) {
    int sys_errno = 0;
    int reason = 0;
    take_ssl_error_reason(&sys_errno, &reason);
    return mk_ssl_error_of(ssl, st, ssl_err, sys_errno, reason, fallback);
}

lean_obj_res mk_ssl_session_dead(const ssl_error_state* st) {
    if (st->input_truncated) {
        return mk_ssl_eof_error();
    }

    if (st->closed_before_handshake) {
        return mk_ssl_protocol_error("the TLS session was closed before it was negotiated");
    }

    return mk_ssl_protocol_error("the TLS session was aborted by an earlier fatal error");
}

lean_obj_res mk_ssl_write_queue_full() {
    ERR_clear_error();
    return lean_io_result_mk_error(lean_mk_io_error_resource_exhausted(ENOBUFS,
        mk_string("the TLS session already holds the maximum amount of unsent plaintext")));
}

lean_obj_res mk_ssl_enqueue_rejected() {
    ERR_clear_error();
    return lean_io_result_mk_error(lean_mk_io_error_resource_exhausted(ENOMEM,
        mk_string("could not buffer the plaintext to send over the TLS session")));
}

#endif

}
