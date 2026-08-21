/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/session.h"

#include "runtime/io.h"
#include "runtime/openssl/context.h"
#include "runtime/openssl/ssl_error.h"

#include <cstring>
#include <limits>
#include <memory>
#include <new>

#ifndef LEAN_EMSCRIPTEN
#include <openssl/err.h>
#include <openssl/x509.h>
#include <openssl/x509_vfy.h>
#include <openssl/x509v3.h>
#endif

namespace lean {

lean_external_class* g_ssl_session_external_class = nullptr;

#ifndef LEAN_EMSCRIPTEN

static void lean_ssl_session_finalizer(void* ptr) {
    lean_ssl_session_object* obj = (lean_ssl_session_object*)ptr;
    SSL_free(obj->ssl);
    delete obj;
}

void initialize_openssl_session() {
    g_ssl_session_external_class = lean_register_external_class(lean_ssl_session_finalizer, [](void*, lean_object*) {});
}

// `SSL_write`, `BIO_write` and `BIO_read` all take their length as an `int`, so a `ByteArray` that
// does not fit has to be refused rather than silently truncated by the cast.
static constexpr size_t ssl_max_io_bytes = (size_t)std::numeric_limits<int>::max();

// `IOWant` is an enum inductive, so it is an unboxed `uint8_t` (`read` = 0, `write` = 1). How it is
// stored depends on the constructor holding it, and the two wrappers below differ:
//
// `Option IOWant` (returned by `handshake`, `write` and `closeNotify`) holds it as a boxed field:
//
//   none          = lean_box(0)                    (Option.none, cidx=0)
//   some .read    = ctor(1){ lean_box(0) }         (Option.some IOWant.read)
//   some .write   = ctor(1){ lean_box(1) }         (Option.some IOWant.write)
//
// `ReadResult` (returned by `read?`) stores it unboxed, in the scalar area of a constructor with no
// object fields:
//
//   data bytes    = ctor(0){ bytes }               (ReadResult.data,   cidx=0, one object field)
//   wantIO .read  = ctor(1) + uint8 0 at offset 0  (ReadResult.wantIO, cidx=1, one scalar field)
//   wantIO .write = ctor(1) + uint8 1 at offset 0
//   closed        = lean_box(2)                    (ReadResult.closed, cidx=2, nullary)
//
// The two encodings share no value: the payload is boxed in one and unboxed in the other, and the
// nullary constructors differ as well (`Option.none` = lean_box(0), `ReadResult.closed` = box(2)).

static lean_obj_res mk_option_iowant_none() {
    return lean_io_result_mk_ok(lean_box(0));
}

static lean_obj_res mk_read_result_closed() {
    return lean_io_result_mk_ok(lean_box(2));
}

static unsigned iowant_of(int ssl_err) { return ssl_err == SSL_ERROR_WANT_READ ? 0 : 1; }

static lean_obj_res mk_option_iowant(int ssl_err) {
    lean_object* r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, lean_box(iowant_of(ssl_err)));
    return lean_io_result_mk_ok(r);
}

static lean_obj_res mk_read_result_want(int ssl_err) {
    lean_object* r = lean_alloc_ctor(1, 0, 1);
    lean_ctor_set_uint8(r, 0, (uint8_t)iowant_of(ssl_err));
    return lean_io_result_mk_ok(r);
}

static lean_obj_res mk_read_result_data(lean_object* bytes) {
    lean_object* r = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(r, 0, bytes);
    return lean_io_result_mk_ok(r);
}

static lean_obj_res report_nothing_to_close(lean_ssl_session_object* obj) {
    if (!obj->pending_writes.empty()) {
        obj->pending_writes.clear();
        obj->pending_bytes = 0;
        return mk_ssl_protocol_error("the TLS session ended before buffered data could be sent");
    }

    return mk_option_iowant_none();
}

static void ssl_session_info_callback(const SSL* ssl, int where, int) {
    if ((where & SSL_CB_HANDSHAKE_DONE) == 0) {
        return;
    }

    lean_ssl_session_object* obj = (lean_ssl_session_object*)SSL_get_app_data(ssl);

    if (obj != nullptr) {
        obj->negotiated = true;
    }
}

enum class ssl_write_step { completed, blocked, failed };
enum class ssl_session_role { server, client };

// `err` is the `SSL_get_error` code behind a `blocked` or `failed` step, and 0 otherwise.
struct ssl_write_result {
    ssl_write_step step;
    int err;
};

// Bounds the backlog `write` may add to once the queue is non-empty.
static constexpr size_t ssl_max_pending_write_bytes = 1 << 20;

// Copies plaintext OpenSSL would not take yet so it can be retried once the socket I/O it is
// waiting on completes.
static bool ssl_enqueue_pending_write(lean_ssl_session_object* obj, const uint8_t* data, size_t size) {
    try {
        obj->pending_writes.emplace_back(data, data + size);
    } catch (std::bad_alloc&) {
        return false;
    }

    obj->pending_bytes += size;
    return true;
}

// `size` must fit in an `int`; `lean_ssl_write` rejects oversized payloads before they can reach
// this function or the pending queue. `SSL_MODE_ENABLE_PARTIAL_WRITE` is not set, so a positive
// return means the whole chunk was taken.
static ssl_write_result try_ssl_write(lean_ssl_session_object* obj, const uint8_t* data, size_t size) {
    if (size == 0) {
        return {ssl_write_step::completed, 0};
    }

    ERR_clear_error();
    int rc = SSL_write(obj->ssl, data, (int)size);
    if (rc > 0) {
        return {ssl_write_step::completed, 0};
    }

    int err = SSL_get_error(obj->ssl, rc);

    if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE) {
        return {ssl_write_step::blocked, err};
    }

    return {ssl_write_step::failed, err};
}

static ssl_write_result try_flush_pending_writes(lean_ssl_session_object* obj) {
    while (!obj->pending_writes.empty()) {
        auto& pw = obj->pending_writes.front();
        ssl_write_result written = try_ssl_write(obj, pw.data(), pw.size());

        if (written.step != ssl_write_step::completed) {
            return written;
        }

        obj->pending_bytes -= pw.size();
        obj->pending_writes.pop_front();
    }

    return {ssl_write_step::completed, 0};
}

static lean_obj_res mk_flush_error(lean_ssl_session_object* obj, int err) {
    return mk_ssl_error(obj->ssl, &obj->err, err, "could not send buffered data over the TLS session");
}

// Flushes the pending-write queue, then builds the `ReadResult.wantIO` that `read?` reports, so the
// caller is told about the socket I/O that is actually outstanding. A failed flush is raised here
// rather than deferred to the next `write`.
static lean_obj_res flush_and_return_want(lean_ssl_session_object* obj, int base_want) {
    ssl_write_result flushed = try_flush_pending_writes(obj);
    if (flushed.step == ssl_write_step::failed) {
        return mk_flush_error(obj, flushed.err);
    }

    return mk_read_result_want(flushed.step == ssl_write_step::blocked ? flushed.err : base_want);
}

// RAII structs.
struct ssl_deleter { void operator()(SSL* ssl) const { SSL_free(ssl); } };
struct bio_deleter { void operator()(BIO* bio) const { BIO_free(bio); } };

// Own the pieces while the session is still being assembled, so no error path has to unwind by hand.
using ssl_ptr = std::unique_ptr<SSL, ssl_deleter>;
using bio_ptr = std::unique_ptr<BIO, bio_deleter>;

static lean_obj_res mk_ssl_session(SSL_CTX* ctx, ssl_session_role role) {
    ERR_clear_error();

    ssl_ptr ssl(SSL_new(ctx));

    if (ssl == nullptr) {
        return mk_openssl_io_error("SSL_new failed");
    }

    bio_ptr read_bio(BIO_new(BIO_s_mem()));
    bio_ptr write_bio(BIO_new(BIO_s_mem()));

    if (read_bio == nullptr || write_bio == nullptr) {
        return mk_openssl_io_error("BIO_new failed");
    }

    SSL_set_bio(ssl.get(), read_bio.release(), write_bio.release());

    if (role == ssl_session_role::server) {
        SSL_set_accept_state(ssl.get());
    } else {
        SSL_set_connect_state(ssl.get());
    }

    std::unique_ptr<lean_ssl_session_object> ssl_obj;

    try {
        ssl_obj.reset(new lean_ssl_session_object());
    } catch (std::bad_alloc&) {
        return mk_openssl_io_error("failed to allocate SSL session object");
    }

    ssl_obj->ssl = ssl.get();

    if (SSL_set_app_data(ssl.get(), ssl_obj.get()) != 1) {
        return mk_openssl_io_error("SSL_set_app_data failed");
    }

    SSL_set_info_callback(ssl.get(), ssl_session_info_callback);

    ssl.release();
    lean_object* obj = lean_ssl_session_object_new(ssl_obj.release());
    lean_mark_mt(obj);

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.SSL.Session.Server.mkImpl (ctx : @& Context.Server) : IO Session */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_mk_server(b_obj_arg ctx_obj) {
    return mk_ssl_session(lean_to_ssl_context(ctx_obj), ssl_session_role::server);
}

/* Std.Internal.SSL.Session.Client.mkImpl (ctx : @& Context.Client) : IO Session */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_mk_client(b_obj_arg ctx_obj) {
    return mk_ssl_session(lean_to_ssl_context(ctx_obj), ssl_session_role::client);
}

// Whether `name` is an IP address in textual form.
static bool ssl_ip_literal(const char* name, char (&out)[46]) {
    size_t len = strlen(name);

    if (len >= 2 && name[0] == '[' && name[len - 1] == ']') {
        name += 1;
        len -= 2;
    }

    if (len >= sizeof(out)) {
        return false;
    }

    memcpy(out, name, len);
    out[len] = '\0';

    ASN1_OCTET_STRING* ip = a2i_IPADDRESS(out);
    if (ip == nullptr) {
        return false;
    }

    ASN1_OCTET_STRING_free(ip);
    return true;
}

/* Std.Internal.SSL.Session.setServerNameImpl (ssl : @& Session) (host : @& String) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_set_server_name(b_obj_arg ssl, b_obj_arg host) {
    ERR_clear_error();

    const char* server_name = lean_string_cstr(host);
    if (strlen(server_name) != lean_string_size(host) - 1) {
        return mk_embedded_nul_error(host);
    }

    lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
    if (ssl_obj->err.failed) {
        return mk_ssl_session_dead(&ssl_obj->err);
    }

    if (!SSL_in_before(ssl_obj->ssl)) {
        return mk_ssl_invalid_argument("the server name must be set before the handshake starts");
    }

    char host_buf[TLSEXT_MAXLEN_host_name + 1];
    size_t host_len = strlen(server_name);

    if (host_len > 0 && host_len <= sizeof(host_buf) && server_name[host_len - 1] == '.') {
        memcpy(host_buf, server_name, host_len - 1);
        host_buf[host_len - 1] = '\0';
        server_name = host_buf;
    }

    if (server_name[0] == '\0') {
        return mk_ssl_invalid_argument("the server name is empty");
    }

    char ip_literal[46];
    bool is_ip = ssl_ip_literal(server_name, ip_literal);

    if (!is_ip && server_name[0] == '[') {
        return mk_ssl_invalid_argument("the bracketed server name is not a valid IP address");
    }

    if (is_ip) {
        // Sets the host name to null, because we cannot put host name as an IP.
        SSL_set_tlsext_host_name(ssl_obj->ssl, nullptr);
    } else if (SSL_set_tlsext_host_name(ssl_obj->ssl, server_name) != 1) {
        return mk_ssl_invalid_argument("the server name is not a valid SNI hostname");
    }

    if (SSL_set1_host(ssl_obj->ssl, is_ip ? ip_literal : server_name) != 1) {
        SSL_set_tlsext_host_name(ssl_obj->ssl, nullptr);
        ssl_obj->err.failed = true;
        return mk_ssl_invalid_argument("the server name cannot be used for certificate verification");
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.SSL.Session.verifyResult (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_verify_result(b_obj_arg ssl) {
    ERR_clear_error();
    lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
    long result = SSL_get_verify_result(ssl_obj->ssl);

    uint64_t code = (result < 0) ? (uint64_t)X509_V_ERR_UNSPECIFIED : (uint64_t)result;
    return lean_io_result_mk_ok(lean_box_uint64(code));
}

/* Std.Internal.SSL.Session.verifyResultString (ssl : @& Session) : IO String */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_verify_result_string(b_obj_arg ssl) {
    ERR_clear_error();
    lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
    long result = SSL_get_verify_result(ssl_obj->ssl);

    const char* msg = X509_verify_cert_error_string(result);
    if (msg == nullptr) {
        msg = "unknown certificate verification error";
    }

    return lean_io_result_mk_ok(lean_mk_string(msg));
}

/* Std.Internal.SSL.Session.handshake (ssl : @& Session) : IO (Option IOWant) */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_handshake(b_obj_arg ssl) {
    ERR_clear_error();

    lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
    if (ssl_obj->err.failed) {
        return mk_ssl_session_dead(&ssl_obj->err);
    }

    int rc = SSL_do_handshake(ssl_obj->ssl);

    if (rc == 1) {
        return mk_option_iowant_none();
    }

    int err = SSL_get_error(ssl_obj->ssl, rc);

    if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE) {
        return mk_option_iowant(err);
    }

    return mk_ssl_error(ssl_obj->ssl, &ssl_obj->err, err, "the TLS handshake failed");
}

/* Std.Internal.SSL.Session.write (ssl : @& Session) (data : @& ByteArray) : IO (Option IOWant) */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_write(b_obj_arg ssl, b_obj_arg data) {
    ERR_clear_error();

    lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
    if (ssl_obj->err.failed) {
        return mk_ssl_session_dead(&ssl_obj->err);
    }

    size_t data_len = lean_sarray_size(data);
    const uint8_t* payload = (const uint8_t*)lean_sarray_cptr(data);

    if (data_len > ssl_max_io_bytes) {
        return mk_ssl_invalid_argument("the data to write is too large");
    }

    if (data_len > 0) {
        if (!ssl_obj->pending_writes.empty()) {
            size_t room = ssl_obj->pending_bytes < ssl_max_pending_write_bytes
                ? ssl_max_pending_write_bytes - ssl_obj->pending_bytes
                : 0;

            if (data_len > room) {
                return mk_ssl_write_queue_full();
            }
        }

        // OpenSSL has not seen this plaintext, so refusing it leaves the session usable.
        if (!ssl_enqueue_pending_write(ssl_obj, payload, data_len)) {
            return mk_ssl_enqueue_rejected();
        }
    }

    ssl_write_result flushed = try_flush_pending_writes(ssl_obj);

    if (flushed.step == ssl_write_step::blocked) {
        return mk_option_iowant(flushed.err);
    }

    if (flushed.step == ssl_write_step::failed) {
        if (data_len > 0 && !ssl_obj->pending_writes.empty()) {
            ssl_obj->pending_bytes -= ssl_obj->pending_writes.back().size();
            ssl_obj->pending_writes.pop_back();
        }

        return mk_ssl_error(ssl_obj->ssl, &ssl_obj->err, flushed.err, "could not send data over the TLS session");
    }

    return mk_option_iowant_none();
}

/* Std.Internal.SSL.Session.read? (ssl : @& Session) (maxBytes : UInt64) : IO ReadResult */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_read(b_obj_arg ssl, uint64_t max_bytes) {
    ERR_clear_error();
    lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
    if (ssl_obj->err.failed) {
        return mk_ssl_session_dead(&ssl_obj->err);
    }

    // `max_bytes == 0` is the peek convention: report whether plaintext is available without
    // consuming it, as a zero-length `.data`. See the `read?` docstring.
    bool peek = max_bytes == 0;
    size_t cap = peek ? 1
                      : (max_bytes < SSL3_RT_MAX_PLAIN_LENGTH ? (size_t)max_bytes : (size_t)SSL3_RT_MAX_PLAIN_LENGTH);

    lean_object* out = lean_alloc_sarray(1, 0, cap);
    void* buf = (void*)lean_sarray_cptr(out);
    int rc = peek ? SSL_peek(ssl_obj->ssl, buf, 1) : SSL_read(ssl_obj->ssl, buf, (int)cap);

    if (rc > 0) {
        lean_sarray_set_size(out, peek ? 0 : (size_t)rc);
        return mk_read_result_data(out);
    }

    int err = SSL_get_error(ssl_obj->ssl, rc);
    lean_dec(out);

    if (err == SSL_ERROR_ZERO_RETURN) {
        return mk_read_result_closed();
    }

    if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE) {
        return flush_and_return_want(ssl_obj, err);
    }

    return mk_ssl_error(ssl_obj->ssl, &ssl_obj->err, err, "could not read data from the TLS session");
}

/* Std.Internal.SSL.Session.feedEncrypted (ssl : @& Session) (data : @& ByteArray) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_feed_encrypted(b_obj_arg ssl, b_obj_arg data) {
    ERR_clear_error();
    lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
    size_t data_len = lean_sarray_size(data);

    if (ssl_obj->input_eof) {
        return mk_ssl_invalid_argument("the encrypted input stream was already ended by feedEof");
    }

    if (ssl_obj->err.failed) {
        return mk_ssl_session_dead(&ssl_obj->err);
    }

    if (data_len == 0) {
        return lean_io_result_mk_ok(lean_box_uint64(0));
    }

    if (data_len > ssl_max_io_bytes) {
        return mk_ssl_invalid_argument("the encrypted data to feed is too large");
    }

    BIO* rbio = SSL_get_rbio(ssl_obj->ssl);
    int rc = BIO_write(rbio, lean_sarray_cptr(data), (int)data_len);
    if (rc > 0) {
        return lean_io_result_mk_ok(lean_box_uint64((uint64_t)rc));
    }

    if (rc == 0) {
        return mk_openssl_io_error("BIO_write: wrote 0 bytes");
    }

    if (BIO_should_retry(rbio)) {
        return mk_openssl_io_error("BIO_write: unexpected retry flag on memory BIO");
    }

    return mk_openssl_io_error("BIO_write failed");
}

/* Std.Internal.SSL.Session.feedEof (ssl : @& Session) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_feed_eof(b_obj_arg ssl) {
    ERR_clear_error();
    lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);

    BIO_set_mem_eof_return(SSL_get_rbio(ssl_obj->ssl), 0);
    ssl_obj->input_eof = true;

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.SSL.Session.drainEncrypted (ssl : @& Session) : IO ByteArray */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_drain_encrypted(b_obj_arg ssl) {
    ERR_clear_error();
    lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
    BIO* write_bio = SSL_get_wbio(ssl_obj->ssl);
    size_t pending = BIO_ctrl_pending(write_bio);

    if (pending == 0) {
        return lean_io_result_mk_ok(lean_mk_empty_byte_array(lean_box(0)));
    }

    if (pending > ssl_max_io_bytes) {
        return mk_openssl_io_error("BIO_pending output too large");
    }

    lean_object* out = lean_alloc_sarray(1, 0, pending);
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
    lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
    size_t pending = BIO_ctrl_pending(SSL_get_wbio(ssl_obj->ssl));
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)pending));
}

/* Std.Internal.SSL.Session.pendingPlaintext (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_plaintext(b_obj_arg ssl) {
    ERR_clear_error();
    lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);

    int pending = SSL_pending(ssl_obj->ssl);
    return lean_io_result_mk_ok(lean_box_uint64(pending > 0 ? (uint64_t)pending : 0));
}

static bool peer_closed(SSL* ssl) { return (SSL_get_shutdown(ssl) & SSL_RECEIVED_SHUTDOWN) != 0; }

// Records the failure the teardown has just hit and answers with what the shutdown can still
// report.
static lean_obj_res finish_nothing_to_close(lean_ssl_session_object* obj) {
    int sys_errno = 0;
    int reason = 0;
    take_ssl_error_reason(&sys_errno, &reason);

    ssl_input_truncated(&obj->err, reason);
    obj->err.failed = true;

    return report_nothing_to_close(obj);
}

// Runs one `SSL_shutdown`. Returns nullptr when our alert went out and the peer's has not arrived,
// leaving the caller to carry on; otherwise the verdict to report.
static lean_obj_res close_notify_shutdown(lean_ssl_session_object* obj) {
    ERR_clear_error();
    int rc = SSL_shutdown(obj->ssl);

    if (rc == 1) {
        return mk_option_iowant_none();
    }

    if (rc == 0) {
        return nullptr;
    }

    int err = SSL_get_error(obj->ssl, rc);
    if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE) {
        return mk_option_iowant(err);
    }

    int sys_errno = 0;
    int reason = 0;
    take_ssl_error_reason(&sys_errno, &reason);

    if (!obj->negotiated) {
        if (!ssl_input_truncated(&obj->err, reason) && obj->input_eof) {
            obj->err.input_truncated = true;
        }

        obj->err.failed = true;
        obj->err.closed_before_handshake = true;
        return report_nothing_to_close(obj);
    }

    return mk_ssl_error_of(obj->ssl, &obj->err, err, sys_errno, reason, "could not shut down the TLS session");
}

// Looks at what is behind the encrypted input without consuming plaintext, which also drives the
// record layer through any post-handshake message waiting there. Returns nullptr when the session
// survived; otherwise the verdict the shutdown reports. `out_rc` receives the `SSL_peek` return
// where the caller distinguishes plaintext in hand from a want.
static lean_obj_res close_notify_peek(lean_ssl_session_object* obj, int* out_rc = nullptr) {
    char buf[1];
    ERR_clear_error();
    int rc = SSL_peek(obj->ssl, buf, 1);
    if (out_rc != nullptr) {
        *out_rc = rc;
    }

    int err = rc > 0 ? SSL_ERROR_NONE : SSL_get_error(obj->ssl, rc);

    // Leaves the error queue empty on every benign outcome, since the `SSL_shutdown` that follows
    // is classified by `SSL_get_error`, which reports any leftover entry as a fatal error.
    if (err == SSL_ERROR_NONE || err == SSL_ERROR_ZERO_RETURN || err == SSL_ERROR_WANT_READ
            || err == SSL_ERROR_WANT_WRITE) {
        ERR_clear_error();
        return nullptr;
    }

    // The peek has just torn the session down. Reporting it here rather than raising is what makes
    // the shutdown answer the same whether or not an earlier call diagnosed the same input first.
    return finish_nothing_to_close(obj);
}

// Plaintext accepted by `write` but not yet encrypted must reach the peer before the alert that
// ends the session; `SSL_shutdown` would leave it in the queue with the caller never learning the
// data was dropped. Only worth attempting once the session is negotiated: before that `SSL_write`
// would drive the handshake instead, so `close_notify_shutdown` reports the loss.
static lean_obj_res close_notify_flush(lean_ssl_session_object* obj) {
    if (!obj->negotiated || obj->pending_writes.empty()) {
        return nullptr;
    }

    ssl_write_result flushed = try_flush_pending_writes(obj);

    // The flush is the last chance to deliver this plaintext, so its failure is the loss the
    // teardown has to hear about rather than a second, separate diagnosis.
    if (flushed.step == ssl_write_step::failed) {
        return finish_nothing_to_close(obj);
    }

    if (flushed.step == ssl_write_step::blocked) {
        return mk_option_iowant(flushed.err);
    }

    return nullptr;
}

// `SSL_shutdown` refuses to run while OpenSSL is part-way through a post-handshake message — a
// TLS 1.3 `NewSessionTicket` split across records, say — and sends nothing at all there. The peek
// drives that message to completion first, since only a read can; without it the shutdown would
// raise on a healthy session whose alert simply has to wait for the rest of that message.
static lean_obj_res close_notify_finish_init(lean_ssl_session_object* obj) {
    if (!obj->negotiated || !SSL_in_init(obj->ssl)) {
        return nullptr;
    }

    if (lean_obj_res finished = close_notify_peek(obj)) {
        return finished;
    }

    if (!SSL_in_init(obj->ssl)) {
        return nullptr;
    }

    // The peek may have taken in the peer's `close_notify` itself: the message can no longer be
    // finished and the alert can no longer go out, so there is nothing left to exchange rather than
    // input to wait for.
    if (peer_closed(obj->ssl)) {
        return report_nothing_to_close(obj);
    }

    // Only more encrypted input can finish the message. A caller looping here terminates because
    // `feedEof` makes the peek above fail rather than ask for input again, which relies on
    // `SSL_OP_IGNORE_UNEXPECTED_EOF` staying unset on the context.
    return mk_option_iowant(SSL_ERROR_WANT_READ);
}

// Our alert has gone out; looks for the peer's without letting `SSL_shutdown` do the reading.
static lean_obj_res close_notify_await_peer(lean_ssl_session_object* obj) {
    if (!obj->negotiated) {
        return nullptr;
    }

    int peek_rc = 0;
    if (lean_obj_res finished = close_notify_peek(obj, &peek_rc)) {
        return finished;
    }

    if (peek_rc > 0) {
        return mk_option_iowant_none();
    }

    if (peer_closed(obj->ssl)) {
        return mk_option_iowant_none();
    }

    // The peek pulled in the start of another post-handshake message; the shutdown below would
    // refuse to run until the rest of it arrives.
    if (SSL_in_init(obj->ssl)) {
        return mk_option_iowant(SSL_ERROR_WANT_READ);
    }

    return nullptr;
}

/* Std.Internal.SSL.Session.closeNotify (ssl : @& Session) : IO (Option IOWant) */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_close_notify(b_obj_arg ssl) {
    ERR_clear_error();
    lean_ssl_session_object* obj = lean_to_ssl_session_object(ssl);
    SSL* s = obj->ssl;

    if (obj->err.failed) {
        return report_nothing_to_close(obj);
    }

    if (obj->negotiated && SSL_in_init(s) && peer_closed(s)) {
        return report_nothing_to_close(obj);
    }

    if (lean_obj_res r = close_notify_flush(obj)) {
        return r;
    }

    if (lean_obj_res r = close_notify_finish_init(obj)) {
        return r;
    }

    if ((SSL_get_shutdown(s) & SSL_SENT_SHUTDOWN) == 0) {
        if (lean_obj_res done = close_notify_shutdown(obj)) {
            return done;
        }
    }

    if (peer_closed(s)) {
        return mk_option_iowant_none();
    }

    if (lean_obj_res r = close_notify_await_peer(obj)) {
        return r;
    }

    if (lean_obj_res done = close_notify_shutdown(obj)) {
        return done;
    }

    return mk_option_iowant(SSL_ERROR_WANT_READ);
}

/* Std.Internal.SSL.Session.negotiatedVersion (ssl : @& Session) : IO String */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_negotiated_version(b_obj_arg ssl) {
    ERR_clear_error();
    lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
    const char* version = SSL_get_version(ssl_obj->ssl);
    return lean_io_result_mk_ok(lean_mk_string(version != nullptr ? version : "unknown"));
}

#else

void initialize_openssl_session() {}

/* Std.Internal.SSL.Session.Server.mkImpl (ctx : @& Context.Server) : IO Session */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_mk_server(b_obj_arg /*ctx_obj*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.Client.mkImpl (ctx : @& Context.Client) : IO Session */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_mk_client(b_obj_arg /*ctx_obj*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.setServerNameImpl (ssl : @& Session) (host : @& String) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_set_server_name(b_obj_arg /*ssl*/, b_obj_arg /*host*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.verifyResult (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_verify_result(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.verifyResultString (ssl : @& Session) : IO String */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_verify_result_string(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.handshake (ssl : @& Session) : IO (Option IOWant) */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_handshake(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.write (ssl : @& Session) (data : @& ByteArray) : IO (Option IOWant) */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_write(b_obj_arg /*ssl*/, b_obj_arg /*data*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.read? (ssl : @& Session) (maxBytes : UInt64) : IO ReadResult */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_read(b_obj_arg /*ssl*/, uint64_t /*max_bytes*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.feedEncrypted (ssl : @& Session) (data : @& ByteArray) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_feed_encrypted(b_obj_arg /*ssl*/, b_obj_arg /*data*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.feedEof (ssl : @& Session) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_feed_eof(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.drainEncrypted (ssl : @& Session) : IO ByteArray */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_drain_encrypted(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.pendingEncrypted (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_encrypted(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.pendingPlaintext (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_plaintext(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.closeNotify (ssl : @& Session) : IO (Option IOWant) */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_close_notify(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.negotiatedVersion (ssl : @& Session) : IO String */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_negotiated_version(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

#endif

}
