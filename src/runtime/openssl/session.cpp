/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/session.h"

#include <cerrno>
#include <climits>
#include <cstring>
#include <string>

#ifndef LEAN_EMSCRIPTEN
#include <openssl/x509v3.h>
#include <openssl/x509_vfy.h>
#endif

namespace lean {

lean_external_class * g_ssl_session_external_class = nullptr;

#ifndef LEAN_EMSCRIPTEN

void lean_ssl_session_finalizer(void * ptr) {
    lean_ssl_session_object * obj = (lean_ssl_session_object*)ptr;
    SSL_free(obj->ssl);
    delete obj->pending_writes;
    free(obj);
}

void initialize_openssl_session() {
    g_ssl_session_external_class = lean_register_external_class(lean_ssl_session_finalizer, [](void * obj, lean_object * f) {
        (void)obj;
        (void)f;
    });
}

/*
 * `IOWant` is an enum inductive, so it is an unboxed `uint8_t` (`read` = 0, `write` = 1). How it is
 * stored depends on the constructor holding it, and the two wrappers below differ:
 *
 * `Option IOWant` (returned by `handshake`, `write` and `closeNotify`) is polymorphic, so its field
 * is a boxed object:
 *
 *   none          = lean_box(0)                    (Option.none, cidx=0)
 *   some .read    = ctor(1){ lean_box(0) }         (Option.some IOWant.read)
 *   some .write   = ctor(1){ lean_box(1) }         (Option.some IOWant.write)
 *
 * `ReadResult` (returned by `read?`) stores it unboxed, in the scalar area of a constructor with no
 * object fields:
 *
 *   data bytes    = ctor(0){ bytes }               (ReadResult.data,   cidx=0, one object field)
 *   wantIO .read  = ctor(1) + uint8 0 at offset 0  (ReadResult.wantIO, cidx=1, one scalar field)
 *   wantIO .write = ctor(1) + uint8 1 at offset 0
 *   closed        = lean_box(2)                    (ReadResult.closed, cidx=2, nullary)
 *
 * NOTE: neither the `wantIO` payload nor the nullary constructors are encoded alike across the two
 * types (`Option.none` = lean_box(0) but `ReadResult.closed` = lean_box(2)). Do not conflate them.
 */
static inline lean_obj_res mk_option_iowant_none() {
    return lean_io_result_mk_ok(lean_box(0));
}

static inline lean_obj_res mk_read_result_closed() {
    return lean_io_result_mk_ok(lean_box(2));
}

static inline lean_obj_res mk_option_iowant_read() {
    lean_object * r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, lean_box(0));
    return lean_io_result_mk_ok(r);
}

static inline lean_obj_res mk_option_iowant_write() {
    lean_object * r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, lean_box(1));
    return lean_io_result_mk_ok(r);
}

static inline lean_obj_res mk_read_result_want_read() {
    lean_object * r = lean_alloc_ctor(1, 0, 1);
    lean_ctor_set_uint8(r, 0, 0);
    return lean_io_result_mk_ok(r);
}

static inline lean_obj_res mk_read_result_want_write() {
    lean_object * r = lean_alloc_ctor(1, 0, 1);
    lean_ctor_set_uint8(r, 0, 1);
    return lean_io_result_mk_ok(r);
}

static inline lean_obj_res mk_read_result_data(lean_object * bytes) {
    lean_object * r = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(r, 0, bytes);
    return lean_io_result_mk_ok(r);
}

static inline lean_obj_res mk_ssl_protocol_error(char const * msg) {
    return lean_io_result_mk_error(lean_mk_io_error_protocol_error(EPROTO, mk_string(msg)));
}

static inline lean_obj_res mk_ssl_eof_error() {
    return lean_io_result_mk_error(lean_mk_io_error_eof(lean_box(0)));
}

// Drains the OpenSSL error queue, keeping the first `errno` an `ERR_LIB_SYS` entry carries and the
// first reason code any other entry carries. Both stay 0 when the queue holds no such entry.
static void take_ssl_error_reason(int * sys_errno, int * reason) {
    unsigned long err;

    while ((err = ERR_get_error()) != 0) {
        if (ERR_GET_LIB(err) == ERR_LIB_SYS) {
            if (*sys_errno == 0) *sys_errno = ERR_GET_REASON(err);
        } else if (*reason == 0) {
            *reason = ERR_GET_REASON(err);
        }
    }
}

// The TLS conditions that map to a fixed message; `nullptr` for anything else.
static char const * ssl_reason_message(int reason) {
    switch (reason) {
    case SSL_R_APPLICATION_DATA_AFTER_CLOSE_NOTIFY:
        return "application data arrived after the TLS session was closed";
    case SSL_R_WRONG_VERSION_NUMBER:
    case SSL_R_UNSUPPORTED_PROTOCOL:
        return "the peer does not support a compatible TLS version";
    case SSL_R_NO_SHARED_CIPHER:
        return "the peer shares no supported TLS cipher suite";
    default:
        return nullptr;
    }
}

// Classifies a failed OpenSSL operation as an `IO.Error`. The error queue is drained and dropped:
// entries such as `error:0A000123:SSL routines::application data after close notify` describe
// library internals and must not become the text of a Lean exception, so the condition is reported
// in TLS terms instead. `fallback` describes the operation for failures with no specific mapping.
static lean_obj_res mk_ssl_error(SSL * ssl, int ssl_err, char const * fallback) {
    int sys_errno = 0;
    int reason = 0;
    take_ssl_error_reason(&sys_errno, &reason);

    // A syscall failing under the BIO is an ordinary IO error that already carries an errno.
    if (sys_errno != 0) return lean_io_result_mk_error(decode_io_error(sys_errno, nullptr));

    if (ssl_err == SSL_ERROR_ZERO_RETURN) {
        return lean_io_result_mk_error(lean_mk_io_error_resource_vanished(EPIPE, mk_string("the peer closed the TLS session")));
    }

    if (reason == SSL_R_CERTIFICATE_VERIFY_FAILED) {
        char const * detail = X509_verify_cert_error_string(SSL_get_verify_result(ssl));
        std::string msg("the peer's certificate could not be verified: ");
        msg += detail != nullptr ? detail : "unknown certificate verification error";
        return mk_ssl_protocol_error(msg.c_str());
    }

    // An unexpected transport EOF reaches us either as this reason code or, with an empty queue,
    // as a bare SSL_ERROR_SYSCALL.
    if (reason == SSL_R_UNEXPECTED_EOF_WHILE_READING) return mk_ssl_eof_error();

    char const * msg = ssl_reason_message(reason);
    if (msg != nullptr) return mk_ssl_protocol_error(msg);

    if (ssl_err == SSL_ERROR_SYSCALL) return mk_ssl_eof_error();

    return mk_ssl_protocol_error(fallback);
}

enum ssl_write_step_ {
    ssl_write_step_completed,
    ssl_write_step_blocked,
    ssl_write_step_failed,
};

enum ssl_pending_write_flush {
    ssl_pending_write_flush_completed,
    ssl_pending_write_flush_blocked,
    ssl_pending_write_flush_failed,
};

enum ssl_session_role {
    ssl_session_role_server,
    ssl_session_role_client,
};

// `size` must fit in an `int`; `lean_ssl_write` rejects oversized payloads before they can reach
// this function or the pending queue.
static ssl_write_step_ ssl_write_step(lean_ssl_session_object * obj, char const * data, size_t size, int * out_err) {
    int rc = SSL_write(obj->ssl, data, (int)size);
    if (rc > 0) return ssl_write_step_completed; // Partial write is disabled!

    int err = SSL_get_error(obj->ssl, rc);
    *out_err = err;
    if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE) {
        return ssl_write_step_blocked;
    }

    // Any other error (including SSL_ERROR_ZERO_RETURN) is fatal; the caller inspects
    // `*out_err` to produce a more specific message.
    return ssl_write_step_failed;
}


static ssl_pending_write_flush try_flush_pending_writes(lean_ssl_session_object * obj, int * out_err) {
    while (!obj->pending_writes->empty()) {
        auto & pw = obj->pending_writes->front();
        ssl_write_step_ step = ssl_write_step(obj, pw.data(), pw.size(), out_err);
        if (step == ssl_write_step_failed) return ssl_pending_write_flush_failed;
        if (step == ssl_write_step_blocked) return ssl_pending_write_flush_blocked;

        obj->pending_writes->pop_front();
    }

    return ssl_pending_write_flush_completed;
}

// Builds the `ReadResult.wantIO` that `read?` reports, flushing the pending-write queue first so the
// caller is told about the socket I/O that is actually outstanding. Only `read?` may call this: the
// result is a `ReadResult`, not an `Option IOWant`.
static lean_obj_res flush_and_return_want(lean_ssl_session_object * obj, int base_want) {
    int flush_err = 0;
    ssl_pending_write_flush flushed = try_flush_pending_writes(obj, &flush_err);
    if (flushed == ssl_pending_write_flush_failed) return mk_ssl_error(obj->ssl, flush_err, "could not send buffered data over the TLS session");

    // Still blocked: the flush's own want supersedes the read's. Fully flushed: a WANT_WRITE from
    // the read is satisfied, so what remains is encrypted input.
    int want = flushed == ssl_pending_write_flush_blocked
        ? flush_err
        : (base_want == SSL_ERROR_WANT_WRITE ? SSL_ERROR_WANT_READ : base_want);

    return want == SSL_ERROR_WANT_READ ? mk_read_result_want_read() : mk_read_result_want_write();
}

static lean_obj_res mk_ssl_session(SSL_CTX * ctx, ssl_session_role role) {
    ERR_clear_error();
    SSL * ssl = SSL_new(ctx);

    if (ssl == nullptr) {
        return mk_openssl_io_error("SSL_new failed");
    }

    BIO * read_bio = BIO_new(BIO_s_mem());
    BIO * write_bio = BIO_new(BIO_s_mem());

    if (read_bio == nullptr || write_bio == nullptr) {
        if (read_bio != nullptr) BIO_free(read_bio);
        if (write_bio != nullptr) BIO_free(write_bio);
        SSL_free(ssl);
        return mk_openssl_io_error("BIO_new failed");
    }

    SSL_set_bio(ssl, read_bio, write_bio);

    if (role == ssl_session_role_server) {
        SSL_set_accept_state(ssl);
    } else {
        SSL_set_connect_state(ssl);
    }

    lean_ssl_session_object * ssl_obj = (lean_ssl_session_object*)malloc(sizeof(lean_ssl_session_object));
    if (ssl_obj == nullptr) {
        SSL_free(ssl);
        return mk_openssl_io_error("failed to allocate SSL session object");
    }

    ssl_obj->ssl = ssl;
    ssl_obj->pending_writes = new (std::nothrow) std::deque<std::vector<char>>();

    if (ssl_obj->pending_writes == nullptr) {
        SSL_free(ssl_obj->ssl);
        free(ssl_obj);
        return mk_openssl_io_error("failed to allocate SSL pending_writes queue");
    }

    lean_object * obj = lean_ssl_session_object_new(ssl_obj);
    lean_mark_mt(obj);

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.SSL.Session.Server.mk (ctx : @& Context.Server) : IO Session.Server */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_mk_server(b_obj_arg ctx_obj) {
    lean_ssl_context_object * ctx = lean_to_ssl_context_object(ctx_obj);
    return mk_ssl_session(ctx->ctx, ssl_session_role_server);
}

/* Std.Internal.SSL.Session.Client.mk (ctx : @& Context.Client) : IO Session.Client */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_mk_client(b_obj_arg ctx_obj) {
    lean_ssl_context_object * ctx = lean_to_ssl_context_object(ctx_obj);
    return mk_ssl_session(ctx->ctx, ssl_session_role_client);
}

/* Std.Internal.SSL.Session.Client.setServerName (ssl : @& Session.Client) (host : @& String) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_set_server_name(b_obj_arg ssl, b_obj_arg host) {
    const char * server_name = lean_string_cstr(host);
    if (strlen(server_name) != lean_string_size(host) - 1) return mk_embedded_nul_error(host);

    ERR_clear_error();

    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);

    // SSL_set_tlsext_host_name sets the SNI extension sent in the ClientHello.
    if (SSL_set_tlsext_host_name(ssl_obj->ssl, server_name) != 1) {
        return mk_ssl_invalid_argument("the server name is not a valid SNI hostname");
    }

    // SSL_set1_host enables post-handshake hostname verification against the certificate
    // CN/SAN. Without this, OpenSSL only validates the certificate chain — not that the
    // certificate actually belongs to the hostname we connected to.
    if (SSL_set1_host(ssl_obj->ssl, server_name) != 1) {
        return mk_ssl_invalid_argument("the server name cannot be used for certificate verification");
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.SSL.Session.verifyResult (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_verify_result(b_obj_arg ssl) {
    ERR_clear_error();
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    long result = SSL_get_verify_result(ssl_obj->ssl);

    // X509 error codes are always non-negative. Map any unexpected negative sentinel to
    // X509_V_ERR_UNSPECIFIED rather than 0, since 0 is X509_V_OK (success) and must not be
    // synthesized for an unknown failure.
    uint64_t code = (result < 0) ? (uint64_t)X509_V_ERR_UNSPECIFIED : (uint64_t)result;
    return lean_io_result_mk_ok(lean_box_uint64(code));
}

/* Std.Internal.SSL.Session.verifyResultString (ssl : @& Session) : IO String */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_verify_result_string(b_obj_arg ssl) {
    ERR_clear_error();
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    long result = SSL_get_verify_result(ssl_obj->ssl);

    const char * msg = X509_verify_cert_error_string(result);
    if (msg == nullptr) {
        msg = "unknown certificate verification error";
    }
    return lean_io_result_mk_ok(lean_mk_string(msg));
}

/* Std.Internal.SSL.Session.handshake (ssl : @& Session) : IO (Option IOWant) */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_handshake(b_obj_arg ssl) {
    ERR_clear_error();

    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    int rc = SSL_do_handshake(ssl_obj->ssl);

    if (rc == 1) {
        return mk_option_iowant_none();
    }

    int err = SSL_get_error(ssl_obj->ssl, rc);
    if (err == SSL_ERROR_WANT_READ) {
        return mk_option_iowant_read();
    }
    if (err == SSL_ERROR_WANT_WRITE) {
        return mk_option_iowant_write();
    }

    // Any other error is fatal for the handshake. In particular SSL_ERROR_ZERO_RETURN
    // (the peer sent a TLS close_notify before the handshake finished) is a protocol
    // error here, not a recoverable retry.
    return mk_ssl_error(ssl_obj->ssl, err, "the TLS handshake failed");
}

/* Std.Internal.SSL.Session.write (ssl : @& Session) (data : @& ByteArray) : IO (Option IOWant) */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_write(b_obj_arg ssl, b_obj_arg data) {
    ERR_clear_error();

    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    size_t data_len = lean_sarray_size(data);
    char const * payload = (char const*)lean_sarray_cptr(data);

    if (data_len > INT_MAX) {
        return mk_ssl_invalid_argument("the data to write is too large");
    }

    // If there are pending writes, try to flush them first to preserve write order.
    // Only attempt the new write directly if the queue fully drains.
    // An empty write (data_len == 0) is used by callers as a pure flush signal;
    // it must not be enqueued, only the want-signal is returned.
    if (!ssl_obj->pending_writes->empty()) {
        int flush_err = 0;
        ssl_pending_write_flush flushed = try_flush_pending_writes(ssl_obj, &flush_err);

        if (flushed == ssl_pending_write_flush_failed) {
            return mk_ssl_error(ssl_obj->ssl, flush_err, "could not send buffered data over the TLS session");
        }

        if (flushed == ssl_pending_write_flush_blocked) {
            if (data_len > 0) {
                ssl_obj->pending_writes->emplace_back(payload, payload + data_len);
            }

            if (flush_err == SSL_ERROR_WANT_READ) {
                return mk_option_iowant_read();
            }

            return mk_option_iowant_write();
        }

        // The queue is clear, fall through to attempt the new write.
    }

    if (data_len == 0) {
        return mk_option_iowant_none();
    }

    int err = 0;
    ssl_write_step_ step = ssl_write_step(ssl_obj, payload, data_len, &err);

    if (step == ssl_write_step_completed) {
        return mk_option_iowant_none();
    }

    // Queue plaintext so it is retried after the required socket I/O completes.
    if (step == ssl_write_step_blocked) {
        ssl_obj->pending_writes->emplace_back(payload, payload + data_len);
        if (err == SSL_ERROR_WANT_READ) {
            return mk_option_iowant_read();
        }
        return mk_option_iowant_write();
    }

    // step == ssl_write_step_failed
    return mk_ssl_error(ssl_obj->ssl, err, "could not send data over the TLS session");
}

/* Std.Internal.SSL.Session.read? (ssl : @& Session) (maxBytes : UInt64) : IO ReadResult */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_read(b_obj_arg ssl, uint64_t max_bytes) {
    ERR_clear_error();
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);

    if (max_bytes == 0) {
        char peek_buf[1];
        int rc = SSL_peek(ssl_obj->ssl, peek_buf, 1);
        if (rc > 0) {
            return mk_read_result_data(lean_mk_empty_byte_array(lean_box(0)));
        }
        int err = SSL_get_error(ssl_obj->ssl, rc);
        if (err == SSL_ERROR_ZERO_RETURN) {
            return mk_read_result_closed();
        }
        // Use flush_and_return_want for both WANT_READ and WANT_WRITE so that any
        // pending_writes are flushed before signalling which I/O the caller needs.
        // This keeps the peek path consistent with the main read path below. Any other
        // error (e.g. SSL_ERROR_SSL on a corrupt record) is fatal and must be surfaced,
        // not masked as a want-I/O signal.
        if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE) {
            return flush_and_return_want(ssl_obj, err);
        }
        return mk_ssl_error(ssl_obj->ssl, err, "could not read data from the TLS session");
    }

    // A single `SSL_read` never yields more than one record's plaintext, so the buffer is capped
    // there rather than at `max_bytes`; that also keeps the `int` conversion below in range.
    size_t cap = max_bytes < SSL3_RT_MAX_PLAIN_LENGTH ? (size_t)max_bytes : (size_t)SSL3_RT_MAX_PLAIN_LENGTH;

    lean_object * out = lean_alloc_sarray(1, 0, cap);
    int rc = SSL_read(ssl_obj->ssl, (void*)lean_sarray_cptr(out), (int)cap);

    if (rc > 0) {
        lean_sarray_set_size(out, (size_t)rc);
        return mk_read_result_data(out);
    }

    lean_dec(out);

    int err = SSL_get_error(ssl_obj->ssl, rc);

    if (err == SSL_ERROR_ZERO_RETURN) {
        return mk_read_result_closed();
    }

    if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE) {
        return flush_and_return_want(ssl_obj, err);
    }

    return mk_ssl_error(ssl_obj->ssl, err, "could not read data from the TLS session");
}

/* Std.Internal.SSL.Session.feedEncrypted (ssl : @& Session) (data : @& ByteArray) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_feed_encrypted(b_obj_arg ssl, b_obj_arg data) {
    ERR_clear_error();
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    size_t data_len = lean_sarray_size(data);

    if (data_len == 0) {
        return lean_io_result_mk_ok(lean_box_uint64(0));
    }

    if (data_len > INT_MAX) {
        return mk_ssl_invalid_argument("the encrypted data to feed is too large");
    }

    BIO * rbio = SSL_get_rbio(ssl_obj->ssl);
    int rc = BIO_write(rbio, lean_sarray_cptr(data), (int)data_len);
    if (rc > 0) {
        return lean_io_result_mk_ok(lean_box_uint64((uint64_t)rc));
    }

    // rc == 0: non-retryable zero-byte write is a hard error, not a short write.
    if (rc == 0) {
        return mk_openssl_io_error("BIO_write: wrote 0 bytes");
    }

    // rc < 0: BIO_s_mem never sets the retry flag; if it does, that is a hard error.
    if (BIO_should_retry(rbio)) {
        return mk_openssl_io_error("BIO_write: unexpected retry flag on memory BIO");
    }

    return mk_openssl_io_error("BIO_write failed");
}

/* Std.Internal.SSL.Session.drainEncrypted (ssl : @& Session) : IO ByteArray */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_drain_encrypted(b_obj_arg ssl) {
    ERR_clear_error();
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    BIO * write_bio = SSL_get_wbio(ssl_obj->ssl);
    size_t pending = BIO_ctrl_pending(write_bio);

    if (pending == 0) {
        return lean_io_result_mk_ok(lean_mk_empty_byte_array(lean_box(0)));
    }

    if (pending > INT_MAX) {
        return mk_openssl_io_error("BIO_pending output too large");
    }

    lean_object * out = lean_alloc_sarray(1, 0, pending);
    int rc = BIO_read(write_bio, (void*)lean_sarray_cptr(out), (int)pending);

    if (rc > 0) {
        lean_sarray_set_size(out, (size_t)rc);
        return lean_io_result_mk_ok(out);
    }

    lean_dec(out);

    if (BIO_should_retry(write_bio)) {
        return lean_io_result_mk_ok(lean_mk_empty_byte_array(lean_box(0)));
    }

    return mk_openssl_io_error("BIO_read failed");
}

/* Std.Internal.SSL.Session.pendingEncrypted (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_encrypted(b_obj_arg ssl) {
    ERR_clear_error();
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    // BIO_ctrl_pending returns size_t (non-negative) in OpenSSL >= 1.1.1;
    // uint64_t is always >= size_t on supported platforms, so the cast is safe.
    size_t pending = BIO_ctrl_pending(SSL_get_wbio(ssl_obj->ssl));
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)pending));
}

/* Std.Internal.SSL.Session.negotiatedVersion (ssl : @& Session) : IO String */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_negotiated_version(b_obj_arg ssl) {
    ERR_clear_error();
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    const char * version = SSL_get_version(ssl_obj->ssl);
    return lean_io_result_mk_ok(lean_mk_string(version != nullptr ? version : "unknown"));
}

/* Std.Internal.SSL.Session.pendingPlaintext (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_plaintext(b_obj_arg ssl) {
    ERR_clear_error();
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)SSL_pending(ssl_obj->ssl)));
}

/* Std.Internal.SSL.Session.closeNotify (ssl : @& Session) : IO (Option IOWant)  */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_close_notify(b_obj_arg ssl) {
    ERR_clear_error();
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);

    if (SSL_is_init_finished(ssl_obj->ssl)) {
        char peek_buf[1];
        int peek_rc = SSL_peek(ssl_obj->ssl, peek_buf, 1);

        if (peek_rc > 0) {
            if ((SSL_get_shutdown(ssl_obj->ssl) & SSL_SENT_SHUTDOWN) == 0) {
                // Sends our alert without entering the read phase, which only runs once
                // SSL_SENT_SHUTDOWN is set.
                int send_rc = SSL_shutdown(ssl_obj->ssl);
                if (send_rc < 0) {
                    int send_err = SSL_get_error(ssl_obj->ssl, send_rc);
                    if (send_err == SSL_ERROR_WANT_WRITE) return mk_option_iowant_write();
                    if (send_err != SSL_ERROR_WANT_READ) {
                        return mk_ssl_error(ssl_obj->ssl, send_err, "could not shut down the TLS session");
                    }
                }
            }
            return mk_option_iowant_read();
        }

        int peek_err = SSL_get_error(ssl_obj->ssl, peek_rc);

        // SSL_ERROR_ZERO_RETURN means the peer's close_notify is buffered, which the shutdown below
        // consumes. Anything but that or a want-I/O signal (e.g. a corrupt record) is fatal.
        if (peek_err != SSL_ERROR_ZERO_RETURN && peek_err != SSL_ERROR_WANT_READ
                && peek_err != SSL_ERROR_WANT_WRITE) {
            return mk_ssl_error(ssl_obj->ssl, peek_err, "could not read data from the TLS session");
        }

        ERR_clear_error();
    }

    int rc = SSL_shutdown(ssl_obj->ssl);

    if (rc == 1) {
        return mk_option_iowant_none();
    }

    if (rc < 0) {
        int err = SSL_get_error(ssl_obj->ssl, rc);
        if (err == SSL_ERROR_WANT_READ) return mk_option_iowant_read();
        if (err == SSL_ERROR_WANT_WRITE) return mk_option_iowant_write();
        return mk_ssl_error(ssl_obj->ssl, err, "could not shut down the TLS session");
    }

    // rc == 0: our close_notify was sent but the peer's has not arrived yet. Retrying immediately
    // lets a peer close_notify that is already buffered in the input BIO (e.g. with memory BIOs)
    // complete the shutdown without a transport round-trip. No application record can precede it:
    // the peek above rules that out, and before the handshake completes there is none to read.
    ERR_clear_error();

    rc = SSL_shutdown(ssl_obj->ssl);
    if (rc == 1) {
        return mk_option_iowant_none();
    }
    if (rc == 0) {
        int err = SSL_get_error(ssl_obj->ssl, rc);
        if (err == SSL_ERROR_WANT_READ) return mk_option_iowant_read();
        if (err == SSL_ERROR_WANT_WRITE) return mk_option_iowant_write();

        // If OpenSSL gives us rc == 0 without a retry hint, fall back to the
        // original "need peer close_notify" interpretation.
        return mk_option_iowant_read();
    }

    int err = SSL_get_error(ssl_obj->ssl, rc);
    if (err == SSL_ERROR_WANT_READ) return mk_option_iowant_read();
    if (err == SSL_ERROR_WANT_WRITE) return mk_option_iowant_write();

    return mk_ssl_error(ssl_obj->ssl, err, "could not shut down the TLS session");
}

#else

void initialize_openssl_session() {}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_mk_server(b_obj_arg /*ctx_obj*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
    return nullptr;
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_mk_client(b_obj_arg /*ctx_obj*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
    return nullptr;
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_set_server_name(b_obj_arg /*ssl*/, b_obj_arg /*host*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
    return nullptr;
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_verify_result(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
    return nullptr;
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_verify_result_string(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
    return nullptr;
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_handshake(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
    return nullptr;
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_write(b_obj_arg /*ssl*/, b_obj_arg /*data*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
    return nullptr;
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_read(b_obj_arg /*ssl*/, uint64_t /*max_bytes*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
    return nullptr;
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_feed_encrypted(b_obj_arg /*ssl*/, b_obj_arg /*data*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
    return nullptr;
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_drain_encrypted(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
    return nullptr;
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_encrypted(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
    return nullptr;
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_plaintext(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
    return nullptr;
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_close_notify(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
    return nullptr;
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_negotiated_version(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
    return nullptr;
}

#endif

}
