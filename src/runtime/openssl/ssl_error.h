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

// The verdict a session records the first time it fails. Every later call reports it rather than
// driving a session that can no longer make progress: OpenSSL degrades a diagnosed failure to a
// bare `SSL_ERROR_SYSCALL` afterwards, which a later call could only report as a generic error.
//
// Each qualifier below is only ever set alongside `failed`, and the two can be set together: a
// shutdown that finds an unnegotiated session on a stream already ended by `feedEof` sets both.
// `mk_ssl_session_dead` reports the truncation first, which is what keeps that session's verdict
// the same whether `read?` or `closeNotify` reached it first.
struct ssl_error_state {
    // Set once a fatal error tore the session down, a shutdown found a session that had never
    // negotiated or tore one down as it peeked or as it made its last attempt to flush, the peer
    // identity could not be bound and so left nothing for the handshake to verify against, or
    // plaintext OpenSSL asked to have replayed could not be buffered.
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

// Reports a failure that has no errno behind it. The OpenSSL error queue is discarded rather than
// appended, so its entries cannot leak into a later, unrelated diagnosis.
lean_obj_res mk_ssl_invalid_argument(const char* msg);

lean_obj_res mk_ssl_eof_error();

// Reports a failure against a path, as an errno-derived IO error where the errno is meaningful.
lean_obj_res mk_ssl_file_error(b_obj_arg file, const char* msg);

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

// The queue could not take plaintext the caller has just submitted. `SSL_write` never saw it, so
// nothing is owed to OpenSSL and the session stays usable: the payload is simply refused.
lean_obj_res mk_ssl_enqueue_rejected();

// The queue could not take plaintext OpenSSL has asked to be replayed. Nothing can present that
// payload again, and OpenSSL refuses a retry carrying different bytes, so the session is finished.
lean_obj_res mk_ssl_enqueue_failed(ssl_error_state* st);

#endif

}
