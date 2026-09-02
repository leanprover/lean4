/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#pragma once

#include <lean/lean.h>
#include "runtime/io.h"
#include "runtime/object.h"
#include "runtime/openssl.h"

#ifndef LEAN_EMSCRIPTEN
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <exception>
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

// The verdict a session records the first time it fails. Every later call reports it rather than
// driving a session that can no longer make progress: OpenSSL degrades a diagnosed failure to a
// bare `SSL_ERROR_SYSCALL` afterwards, which a later call could only report as a generic error.
//
// Each qualifier below is only ever set alongside `failed`, and the two can be set together: a
// shutdown that finds an unnegotiated session on a stream already ended by `feedEof` sets both.
// `mk_ssl_session_dead` reports the truncation first, which is what keeps that session's verdict
// the same whether `read` or `closeNotify` reached it first.
struct ssl_error_state {
    // Set once a fatal error tore the session down, a shutdown found a session that had never
    // negotiated or tore one down as it peeked or as it made its last attempt to flush, the peer
    // identity could not be bound and so left nothing for the handshake to verify against,
    // plaintext OpenSSL asked to have replayed could not be buffered, or a memory BIO asked to
    // flush, which only an allocation failure inside it can mean.
    bool failed;
    // Set when a shutdown finished a session that had never negotiated, so it is not reported as
    // having hit a fatal error it never hit.
    bool closed_before_handshake;
    // Set once the input stream is known to have been truncated — diagnosed by OpenSSL, or inferred
    // from `input_eof` where a shutdown never reads and so cannot be told. This is the one failure
    // that has to keep its own classification: `failed` alone would report it as a protocol error
    // rather than the end of stream it is.
    bool input_truncated;
};

// Drains the OpenSSL error queue and returns a single error message combining up to 10 entries.
lean_object* mk_openssl_error(const char* where);
inline lean_obj_res mk_openssl_io_error(const char* where) { return lean_io_result_mk_error(mk_openssl_error(where)); }

lean_obj_res mk_ssl_protocol_error(const char* msg);

// Reports a failure of the session's own plumbing — an allocation, or a memory BIO behaving in a way
// it cannot. The OpenSSL error queue is discarded rather than rendered into the message: its text
// names library internals, which is the same reason `mk_ssl_error` maps reason codes to prose.
lean_obj_res mk_ssl_internal_error(const char* msg);

// Rejects a path whose bytes cannot reach the OS, which takes it as a NUL-terminated string and so
// would silently act on a prefix. Returns `nullptr` when the path is fine to pass on.
lean_obj_res reject_embedded_nul(b_obj_arg path);

// Reports a failure that has no errno behind it. The OpenSSL error queue is discarded rather than
// appended, so its entries cannot leak into a later, unrelated diagnosis.
lean_obj_res mk_ssl_invalid_argument(const char* msg);

// Reports a failure against a path. `errnum` is the `errno` the open failed with, or 0 for a
// failure with no OS error behind it (unparsable PEM, a key that does not match its certificate).
lean_obj_res mk_ssl_file_error(b_obj_arg file, char const * msg, int errnum = 0);

// Reports a failure against PEM material, naming the path when there is one to name.
lean_obj_res mk_pem_error(pem_source src, char const * msg, int errnum = 0);

// Whether a certificate was turned away on policy grounds rather than being unreadable as PEM.
bool rejected_by_security_level();

// Drains the OpenSSL error queue, keeping the `errno` the first `ERR_LIB_SYS` entry carries and the
// reason code the first `ERR_LIB_SSL` entry carries. Both stay 0 when the queue holds no such entry,
// so an entry whose own code is 0 is passed over rather than recorded.
//
// Reason codes are numbered per library, so entries raised by X509, ASN1, PEM and friends are
// dropped rather than compared against the `SSL_R_*` constants the mapping below switches on, as are
// the library-wide `ERR_R_*` conditions whichever library raised them. Among the SSL entries the
// first is the specific one: `ERR_get_error` is FIFO, and OpenSSL raises the condition it diagnosed
// before any generic entry it adds while unwinding.
void take_ssl_error_reason(int* sys_errno, int* reason);

// Whether a failure describes the encrypted input stream ending mid-stream rather than a protocol
// fault. OpenSSL diagnoses the truncation once, so the verdict is recorded in `st` for the later
// calls that `mk_ssl_session_dead` answers.
bool ssl_input_truncated(ssl_error_state* st, int reason);

// Classifies a failed OpenSSL operation as an `IO.Error` from an already-drained error queue.
// `fallback` describes the operation for failures with no specific mapping.
lean_obj_res mk_ssl_error_of(SSL* ssl, ssl_error_state* st, int ssl_err, int sys_errno, int reason,
                             const char* fallback);

// As `mk_ssl_error_of`, draining the queue first.
//
// Only the reason code survives the queue: OpenSSL's rendered text, such as
// `error:0A000123:SSL routines::application data after close notify`, names library internals and
// must not become the text of a Lean exception, so the code is mapped to a TLS-level message.
lean_obj_res mk_ssl_error(SSL* ssl, ssl_error_state* st, int ssl_err, const char* fallback);

// Reports the condition that already finished the session, for a call made after the fact. Only the
// truncated stream keeps its own classification; every other fatal error is a protocol failure.
lean_obj_res mk_ssl_session_dead(const ssl_error_state* st);

lean_obj_res mk_ssl_write_queue_full();

// The caller has not drained the encrypted output, which is the buffer that actually grows.
lean_obj_res mk_ssl_output_backlog_full();

// The caller has not read the encrypted input it fed, so a peer streaming at line rate would grow
// the input BIO without bound. Draining it with `read` is the way back.
lean_obj_res mk_ssl_input_backlog_full();

// The queue could not take plaintext the caller has just submitted. `SSL_write` never saw it, so
// nothing is owed to OpenSSL and the session stays usable: the payload is simply refused.
lean_obj_res mk_ssl_enqueue_rejected();

// Runs an entry point behind the three guards every one of them needs: OpenSSL initialized before
// any `ERR_*` call can register `atexit(OPENSSL_cleanup)` behind `OPENSSL_INIT_NO_ATEXIT`'s back,
// an empty error queue so a stale entry cannot be read as this call's diagnosis, and no C++
// exception escaping into Lean-generated code, which has no landing pad and would `std::terminate`.
template<typename F>
static inline lean_obj_res ssl_entry_point(F && run) {
    try {
        if (!ensure_openssl_initialized()) {
            return lean_io_result_mk_error(lean_mk_io_user_error(mk_string("OPENSSL_init_ssl failed")));
        }

        ERR_clear_error();
        return run();
    } catch (std::exception & ex) {
        return lean_io_result_mk_error(lean_mk_io_user_error(mk_string(ex.what())));
    }
}

#endif

}
