/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/session.h"

#include <climits>
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
 * `Option IOWant` encoding (used by `handshake` and `write`):
 *
 *   none          = lean_box(0)               (Option.none, cidx=0)
 *   some .read    = ctor(1){ lean_box(0) }    (Option.some IOWant.read)
 *   some .write   = ctor(1){ lean_box(1) }    (Option.some IOWant.write)
 *
 * `ReadResult` encoding (used by `read?`):
 *
 *   data bytes    = ctor(0){ bytes }          (ReadResult.data,    cidx=0, non-nullary)
 *   wantIO .read  = ctor(1){ lean_box(0) }    (ReadResult.wantIO,  cidx=1, non-nullary)
 *   wantIO .write = ctor(1){ lean_box(1) }    (ReadResult.wantIO,  cidx=1, non-nullary)
 *   closed        = lean_box(2)               (ReadResult.closed,  cidx=2, nullary)
 *
 * NOTE: these two types do NOT share a common encoding for their nullary constructors.
 * Option.none = lean_box(0), ReadResult.closed = lean_box(2). Do not conflate them.
 */
static inline lean_obj_res mk_option_iowant_none() {
    return lean_io_result_mk_ok(lean_box(0));
}

static inline lean_obj_res mk_read_result_closed() {
    return lean_io_result_mk_ok(lean_box(2));
}

static inline lean_obj_res mk_ssl_result_want_read() {
    lean_object * r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, lean_box(0));
    return lean_io_result_mk_ok(r);
}

static inline lean_obj_res mk_ssl_result_want_write() {
    lean_object * r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, lean_box(1));
    return lean_io_result_mk_ok(r);
}

static inline lean_obj_res mk_read_result_data(lean_object * bytes) {
    lean_object * r = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(r, 0, bytes);
    return lean_io_result_mk_ok(r);
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

static ssl_write_step_ ssl_write_step(lean_ssl_session_object * obj, char const * data, size_t size, int * out_err) {
    if (size > INT_MAX) {
        *out_err = SSL_ERROR_SSL;
        return ssl_write_step_failed;
    }

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

static ssl_pending_write_flush try_flush_pending_writes(lean_ssl_session_object * obj, int * out_err);

static lean_obj_res flush_and_return_want(lean_ssl_session_object * obj, int base_want) {

    int flush_err = 0;
    ssl_pending_write_flush flushed = try_flush_pending_writes(obj, &flush_err);
    if (flushed == ssl_pending_write_flush_failed) return mk_openssl_io_error("pending SSL write flush failed", flush_err);

    int want;

    if (flushed == ssl_pending_write_flush_blocked) {
        // Still blocked: use the flush's want if it differs from SSL_read's want.
        want = (flush_err != base_want) ? flush_err : base_want;
    } else {
        // Fully flushed: WANT_WRITE is satisfied; now we need encrypted input.
        want = (base_want == SSL_ERROR_WANT_WRITE) ? SSL_ERROR_WANT_READ : base_want;
    }

    return want == SSL_ERROR_WANT_READ ? mk_ssl_result_want_read() : mk_ssl_result_want_write();
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
    ERR_clear_error();

    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    const char * server_name = lean_string_cstr(host);

    // SSL_set_tlsext_host_name sets the SNI extension sent in the ClientHello.
    if (SSL_set_tlsext_host_name(ssl_obj->ssl, server_name) != 1) {
        return mk_openssl_io_error("SSL_set_tlsext_host_name failed");
    }

    // SSL_set1_host enables post-handshake hostname verification against the certificate
    // CN/SAN. Without this, OpenSSL only validates the certificate chain — not that the
    // certificate actually belongs to the hostname we connected to.
    if (SSL_set1_host(ssl_obj->ssl, server_name) != 1) {
        return mk_openssl_io_error("SSL_set1_host failed");
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
        return mk_ssl_result_want_read();
    }
    if (err == SSL_ERROR_WANT_WRITE) {
        return mk_ssl_result_want_write();
    }

    // Any other error is fatal for the handshake. In particular SSL_ERROR_ZERO_RETURN
    // (the peer sent a TLS close_notify before the handshake finished) is a protocol
    // error here, not a recoverable retry.
    return mk_openssl_io_error("SSL_do_handshake failed", err);
}

/* Std.Internal.SSL.Session.write (ssl : @& Session) (data : @& ByteArray) : IO (Option IOWant) */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_write(b_obj_arg ssl, b_obj_arg data) {
    ERR_clear_error();

    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    size_t data_len = lean_sarray_size(data);
    char const * payload = (char const*)lean_sarray_cptr(data);

    // If there are pending writes, try to flush them first to preserve write order.
    // Only attempt the new write directly if the queue fully drains.
    // An empty write (data_len == 0) is used by callers as a pure flush signal;
    // it must not be enqueued, only the want-signal is returned.
    if (!ssl_obj->pending_writes->empty()) {
        int flush_err = 0;
        ssl_pending_write_flush flushed = try_flush_pending_writes(ssl_obj, &flush_err);

        if (flushed == ssl_pending_write_flush_failed) {
            return mk_openssl_io_error("pending SSL write flush failed", flush_err);
        }

        if (flushed == ssl_pending_write_flush_blocked) {
            if (data_len > 0) {
                ssl_obj->pending_writes->emplace_back(payload, payload + data_len);
            }

            if (flush_err == SSL_ERROR_WANT_READ) {
                return mk_ssl_result_want_read();
            }

            return mk_ssl_result_want_write();
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
            return mk_ssl_result_want_read();
        }
        return mk_ssl_result_want_write();
    }

    // step == ssl_write_step_failed
    if (err == SSL_ERROR_ZERO_RETURN) {
        return mk_openssl_io_error("SSL_write failed: peer closed the TLS session", err);
    }

    return mk_openssl_io_error("SSL_write failed", err);
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
        return mk_openssl_io_error("SSL_peek failed", err);
    }

    if (max_bytes > INT_MAX) {
        max_bytes = INT_MAX;
    }

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

    return mk_openssl_io_error("SSL_read failed", err);
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
        return mk_openssl_io_error("BIO_write input too large");
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
    int rc = SSL_shutdown(ssl_obj->ssl);

    if (rc == 1) {
        return mk_option_iowant_none();
    }

    if (rc < 0) {
        int err = SSL_get_error(ssl_obj->ssl, rc);
        if (err == SSL_ERROR_WANT_READ) return mk_ssl_result_want_read();
        if (err == SSL_ERROR_WANT_WRITE) return mk_ssl_result_want_write();
        return mk_openssl_io_error("SSL_shutdown failed", err);
    }

    // rc == 0: our close_notify was sent. Immediately retry: if the peer's close_notify is
    // already buffered in the input BIO (e.g. with memory BIOs), SSL_shutdown will
    // consume it and return 1 without requiring a transport round-trip.
    ERR_clear_error();

    rc = SSL_shutdown(ssl_obj->ssl);
    if (rc == 1) {
        return mk_option_iowant_none();
    }
    if (rc == 0) {
        int err = SSL_get_error(ssl_obj->ssl, rc);
        if (err == SSL_ERROR_WANT_READ) return mk_ssl_result_want_read();
        if (err == SSL_ERROR_WANT_WRITE) return mk_ssl_result_want_write();

        // If OpenSSL gives us rc == 0 without a retry hint, fall back to the
        // original "need peer close_notify" interpretation.
        return mk_ssl_result_want_read();
    }

    int err = SSL_get_error(ssl_obj->ssl, rc);
    if (err == SSL_ERROR_WANT_READ) return mk_ssl_result_want_read();
    if (err == SSL_ERROR_WANT_WRITE) return mk_ssl_result_want_write();

    return mk_openssl_io_error("SSL_shutdown failed", err);
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
