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

// `handshake`, `write` and `closeNotify` answer `Bool`: `true` when the operation finished, `false`
// when it needs more encrypted input from the peer. `ReadResult` is an inductive whose two nullary
// constructors are boxed indices:
//
//   data bytes = ctor(0){ bytes }   (cidx=0, one object field)
//   wantRead   = lean_box(1)        (cidx=1, nullary)
//   closed     = lean_box(2)        (cidx=2, nullary)

static lean_obj_res mk_step_done() {
    return lean_io_result_mk_ok(lean_box(1));
}

static lean_obj_res mk_step_want_read() {
    return lean_io_result_mk_ok(lean_box(0));
}

static lean_obj_res mk_read_result_want_read() {
    return lean_io_result_mk_ok(lean_box(1));
}

static lean_obj_res mk_read_result_closed() {
    return lean_io_result_mk_ok(lean_box(2));
}

static lean_obj_res mk_read_result_data(lean_object* bytes) {
    lean_object* r = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(r, 0, bytes);
    return lean_io_result_mk_ok(r);
}

static lean_obj_res report_nothing_to_close(lean_ssl_session_object* obj) {
    if (obj->pending_bytes != 0) {
        obj->pending_writes.clear();
        obj->pending_bytes = 0;
        return mk_ssl_protocol_error("the TLS session ended before buffered data could be sent");
    }

    return mk_step_done();
}

static bool peer_closed(SSL* ssl) { return (SSL_get_shutdown(ssl) & SSL_RECEIVED_SHUTDOWN) != 0; }

// Frees plaintext a finished session can no longer deliver, keeping `pending_bytes` so the teardown
// still reports the loss. Holding the buffers until the object is finalized would retain up to the
// queue bound — or a whole oversized payload, which the bound exempts — on a session that is dead.
static void release_pending_writes(lean_ssl_session_object* obj) {
    obj->pending_writes.clear();
    obj->pending_writes.shrink_to_fit();
}

// Both BIOs are memory-backed and a memory BIO never fills, so `SSL_ERROR_WANT_WRITE` cannot mean
// "the transport is full" here: it is a failure of the session's own plumbing, and no output the
// caller could flush would clear it. Finishing the session is what keeps it from being handed back
// as a wait nothing can satisfy, which a caller would retry forever. Returns `nullptr` for a plain
// read want, which the caller passes on.
static lean_obj_res reject_want_write(lean_ssl_session_object* obj, int ssl_err) {
    if (ssl_err != SSL_ERROR_WANT_WRITE) {
        return nullptr;
    }

    obj->err.failed = true;
    release_pending_writes(obj);

    return mk_ssl_internal_error(
        "the TLS session asked to flush encrypted output, which a memory BIO never requires");
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

// Bounds the plaintext `write` may retain behind a payload OpenSSL has not taken yet.
static constexpr size_t ssl_max_pending_write_bytes = 1 << 20;

// Bounds the encrypted output the caller has not drained. `SSL_write` into a memory BIO never
// blocks, so this — not the pending-write queue — is the buffer that grows on the ordinary path,
// and nothing else stops a caller that keeps writing without ever calling `drainEncrypted`.
static constexpr size_t ssl_max_unsent_encrypted_bytes = 4 << 20;

// Bounds the encrypted input the caller has fed but not yet read back as plaintext. The input BIO
// is the buffer a hostile *peer* can grow, so it needs its own bound: `read` consumes one record per
// call, and nothing else drains it.
static constexpr size_t ssl_max_unread_encrypted_bytes = 4 << 20;

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

// Diagnoses a failed operation and, where that finished the session, releases the plaintext it was
// still holding.
static lean_obj_res fail_session(lean_ssl_session_object* obj, int err, const char* fallback) {
    lean_obj_res diagnosis = mk_ssl_error(obj->ssl, &obj->err, err, fallback);

    if (obj->err.failed) {
        release_pending_writes(obj);
    }

    return diagnosis;
}

static lean_obj_res mk_flush_error(lean_ssl_session_object* obj, int err) {
    return fail_session(obj, err, "could not send buffered data over the TLS session");
}

// Flushes the pending-write queue, then builds the `ReadResult.wantRead` that `read` reports. A
// failed flush is raised here rather than deferred to the next `write`.
static lean_obj_res flush_and_return_want(lean_ssl_session_object* obj, int base_want) {
    ssl_write_result flushed = try_flush_pending_writes(obj);
    if (flushed.step == ssl_write_step::failed) {
        return mk_flush_error(obj, flushed.err);
    }

    int want = flushed.step == ssl_write_step::blocked ? flushed.err : base_want;

    if (lean_obj_res rejected = reject_want_write(obj, want)) {
        return rejected;
    }

    return mk_read_result_want_read();
}

// RAII structs.
struct ssl_deleter { void operator()(SSL* ssl) const { SSL_free(ssl); } };
struct bio_deleter { void operator()(BIO* bio) const { BIO_free(bio); } };

// Own the pieces while the session is still being assembled, so no error path has to unwind by hand.
using ssl_ptr = std::unique_ptr<SSL, ssl_deleter>;
using bio_ptr = std::unique_ptr<BIO, bio_deleter>;

static lean_obj_res mk_ssl_session(SSL_CTX* ctx, ssl_session_role role) {
    ssl_ptr ssl(SSL_new(ctx));

    if (ssl == nullptr) {
        return mk_ssl_internal_error("SSL_new failed");
    }

    bio_ptr read_bio(BIO_new(BIO_s_mem()));
    bio_ptr write_bio(BIO_new(BIO_s_mem()));

    if (read_bio == nullptr || write_bio == nullptr) {
        return mk_ssl_internal_error("BIO_new failed");
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
        return mk_ssl_internal_error("failed to allocate SSL session object");
    }

    ssl_obj->ssl = ssl.get();

    if (SSL_set_app_data(ssl.get(), ssl_obj.get()) != 1) {
        return mk_ssl_internal_error("SSL_set_app_data failed");
    }

    SSL_set_info_callback(ssl.get(), ssl_session_info_callback);

    ssl.release();
    lean_object* obj = lean_ssl_session_object_new(ssl_obj.release());
    lean_mark_mt(obj);

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.SSL.Session.Server.mkImpl (ctx : @& Context.Server) : IO Session */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_mk_server(b_obj_arg ctx_obj) {
    return ssl_entry_point([&] {
        return mk_ssl_session(lean_to_ssl_context(ctx_obj), ssl_session_role::server);
    });
}

/* Std.Internal.SSL.Session.Client.mkImpl (ctx : @& Context.Client) : IO Session */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_mk_client(b_obj_arg ctx_obj) {
    return ssl_entry_point([&] {
        return mk_ssl_session(lean_to_ssl_context(ctx_obj), ssl_session_role::client);
    });
}

// Whether `name` is an IP address in textual form, writing it to `out` without the brackets a URI
// authority spells IPv6 with.
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
    return ssl_entry_point([&] {
        if (lean_obj_res err = reject_embedded_nul(host)) {
            return err;
        }

        const char* server_name = lean_string_cstr(host);
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
            // No SNI for a literal address: RFC 6066 §3 forbids one there.
            SSL_set_tlsext_host_name(ssl_obj->ssl, nullptr);
        } else if (SSL_set_tlsext_host_name(ssl_obj->ssl, server_name) != 1) {
            return mk_ssl_invalid_argument("the server name is not a valid SNI hostname");
        }

        // `SSL_set1_host` binds a DNS name or an IP address depending on its argument, and before
        // openssl/openssl#27457 it left the other kind in place, so a second call verified against a
        // name the caller had withdrawn. Clearing both first is correct on every 3.x.
        X509_VERIFY_PARAM* param = SSL_get0_param(ssl_obj->ssl);
        X509_VERIFY_PARAM_set1_host(param, nullptr, 0);
        X509_VERIFY_PARAM_set1_ip(param, nullptr, 0);

        if (SSL_set1_host(ssl_obj->ssl, is_ip ? ip_literal : server_name) != 1) {
            SSL_set_tlsext_host_name(ssl_obj->ssl, nullptr);
            ssl_obj->err.failed = true;
            release_pending_writes(ssl_obj);
            return mk_ssl_invalid_argument("the server name cannot be used for certificate verification");
        }

        return lean_io_result_mk_ok(lean_box(0));
    });
}

/* Std.Internal.SSL.Session.verifyResult (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_verify_result(b_obj_arg ssl) {
    return ssl_entry_point([&] {
        lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
        long result = SSL_get_verify_result(ssl_obj->ssl);

        uint64_t code = (result < 0) ? (uint64_t)X509_V_ERR_UNSPECIFIED : (uint64_t)result;
        return lean_io_result_mk_ok(lean_box_uint64(code));
    });
}

/* Std.Internal.SSL.Session.verifyResultString (ssl : @& Session) : IO String */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_verify_result_string(b_obj_arg ssl) {
    return ssl_entry_point([&] {
        lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
        long result = SSL_get_verify_result(ssl_obj->ssl);

        const char* msg = X509_verify_cert_error_string(result);
        if (msg == nullptr) {
            msg = "unknown certificate verification error";
        }

        return lean_io_result_mk_ok(lean_mk_string(msg));
    });
}

/* Std.Internal.SSL.Session.peerNameImpl (ssl : @& Session) : IO (Option String) */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_peer_name(b_obj_arg ssl) {
    return ssl_entry_point([&] {
        lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
        if (ssl_obj->err.failed) {
            return mk_ssl_session_dead(&ssl_obj->err);
        }

        // Recorded by `check_id`, which runs before the signature, validity and name-constraint
        // checks — so a name survives a verification that then fails, and this is only an
        // authentication verdict on a session that has not finished. An `iPAddress` match records
        // no name.
        const char* name = SSL_get0_peername(ssl_obj->ssl);

        if (name == nullptr) {
            return lean_io_result_mk_ok(lean_box(0));
        }

        lean_object* some = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(some, 0, lean_mk_string(name));

        return lean_io_result_mk_ok(some);
    });
}

/* Std.Internal.SSL.Session.handshake (ssl : @& Session) : IO Bool */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_handshake(b_obj_arg ssl) {
    return ssl_entry_point([&] {
        lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
        if (ssl_obj->err.failed) {
            return mk_ssl_session_dead(&ssl_obj->err);
        }

        int rc = SSL_do_handshake(ssl_obj->ssl);

        if (rc == 1) {
            return mk_step_done();
        }

        int err = SSL_get_error(ssl_obj->ssl, rc);

        if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE) {
            if (lean_obj_res rejected = reject_want_write(ssl_obj, err)) {
                return rejected;
            }

            return mk_step_want_read();
        }

        return fail_session(ssl_obj, err, "the TLS handshake failed");
    });
}

/* Std.Internal.SSL.Session.write (ssl : @& Session) (data : @& ByteArray) : IO Bool */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_write(b_obj_arg ssl, b_obj_arg data) {
    return ssl_entry_point([&] {
        lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
        if (ssl_obj->err.failed) {
            return mk_ssl_session_dead(&ssl_obj->err);
        }

        size_t data_len = lean_sarray_size(data);
        const uint8_t* payload = (const uint8_t*)lean_sarray_cptr(data);

        if (data_len > ssl_max_io_bytes) {
            return mk_ssl_invalid_argument("the data to write is too large");
        }

        // Encrypted output the caller has not drained is what actually accumulates, so plaintext is
        // refused once this write would carry the backlog past the bound — testing what is already
        // there would let one payload overshoot it by its own size. Two writes are exempt: an empty
        // one, since flushing the queue is part of the way back, and one against a fully drained
        // session, which has nothing to pile onto and would otherwise have no way to send a payload
        // larger than the bound at all.
        size_t unsent = BIO_ctrl_pending(SSL_get_wbio(ssl_obj->ssl));

        if (data_len > 0 && unsent > 0 && unsent + data_len > ssl_max_unsent_encrypted_bytes) {
            return mk_ssl_output_backlog_full();
        }

        // The backlog is flushed before it is judged. A bound applied to a queue that would drain here
        // refuses plaintext the session can take, and keeps refusing it: the raise would return before
        // the flush that clears the backlog, so the same write fails on every retry.
        ssl_write_result flushed = try_flush_pending_writes(ssl_obj);

        if (flushed.step == ssl_write_step::failed) {
            return fail_session(ssl_obj, flushed.err, "could not send data over the TLS session");
        }

        bool blocked = flushed.step == ssl_write_step::blocked;

        // Judged before the payload is taken anywhere, so the raise leaves `data` unaccepted.
        if (blocked) {
            if (lean_obj_res rejected = reject_want_write(ssl_obj, flushed.err)) {
                return rejected;
            }
        }

        if (data_len > 0 && blocked) {
            // The queue cannot drain, so this payload would be retained on top of it.
            size_t room = ssl_obj->pending_bytes < ssl_max_pending_write_bytes
                ? ssl_max_pending_write_bytes - ssl_obj->pending_bytes
                : 0;

            if (data_len > room) {
                return mk_ssl_write_queue_full();
            }

            // OpenSSL has not seen this plaintext, so refusing it leaves the session usable.
            if (!ssl_enqueue_pending_write(ssl_obj, payload, data_len)) {
                return mk_ssl_enqueue_rejected();
            }
        } else if (data_len > 0) {
            // Nothing is queued ahead of it, so the payload goes straight to OpenSSL. A negotiated
            // session takes it whole and retains nothing, which is the ordinary path: no copy is made
            // and there is no backlog to bound.
            ssl_write_result written = try_ssl_write(ssl_obj, payload, data_len);

            if (written.step == ssl_write_step::failed) {
                return fail_session(ssl_obj, written.err, "could not send data over the TLS session");
            }

            if (written.step == ssl_write_step::blocked) {
                if (lean_obj_res rejected = reject_want_write(ssl_obj, written.err)) {
                    return rejected;
                }

                // Retained so it can be replayed verbatim, which `SSL_write` requires of a write it
                // could not take. This one payload the bound cannot refuse — OpenSSL has already been
                // offered it — but everything queued behind it is bounded above.
                if (!ssl_enqueue_pending_write(ssl_obj, payload, data_len)) {
                    return mk_ssl_enqueue_rejected();
                }

                flushed = written;
                blocked = true;
            }
        }

        return blocked ? mk_step_want_read() : mk_step_done();
    });
}

/* Std.Internal.SSL.Session.read (ssl : @& Session) (maxBytes : UInt64) : IO ReadResult */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_read(b_obj_arg ssl, uint64_t max_bytes) {
    return ssl_entry_point([&] {
        lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
        if (ssl_obj->err.failed) {
            return mk_ssl_session_dead(&ssl_obj->err);
        }

        // One TLS record's worth is the most a single `SSL_read` can produce, so a larger request
        // cannot be served in one call anyway. A `0` would make `SSL_read` report a clean shutdown.
        size_t cap = max_bytes == 0 ? 1
                                    : (max_bytes < SSL3_RT_MAX_PLAIN_LENGTH ? (size_t)max_bytes
                                                                            : (size_t)SSL3_RT_MAX_PLAIN_LENGTH);

        lean_object* out = lean_alloc_sarray(1, 0, cap);
        int rc = SSL_read(ssl_obj->ssl, (void*)lean_sarray_cptr(out), (int)cap);

        if (rc > 0) {
            lean_sarray_set_size(out, (size_t)rc);
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

        return fail_session(ssl_obj, err, "could not read data from the TLS session");
    });
}

/* Std.Internal.SSL.Session.peek (ssl : @& Session) : IO ReadResult */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_peek(b_obj_arg ssl) {
    return ssl_entry_point([&] {
        lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
        if (ssl_obj->err.failed) {
            return mk_ssl_session_dead(&ssl_obj->err);
        }

        // Reports availability without consuming, so the byte read here is put back by `SSL_peek`
        // and never reaches the caller: `.data` is always empty.
        char probe;
        int rc = SSL_peek(ssl_obj->ssl, &probe, 1);

        if (rc > 0) {
            return mk_read_result_data(lean_mk_empty_byte_array(lean_box(0)));
        }

        int err = SSL_get_error(ssl_obj->ssl, rc);

        if (err == SSL_ERROR_ZERO_RETURN) {
            return mk_read_result_closed();
        }

        if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE) {
            return flush_and_return_want(ssl_obj, err);
        }

        return fail_session(ssl_obj, err, "could not read data from the TLS session");
    });
}

/* Std.Internal.SSL.Session.feedEncrypted (ssl : @& Session) (data : @& ByteArray) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_feed_encrypted(b_obj_arg ssl, b_obj_arg data) {
    return ssl_entry_point([&] {
        lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
        size_t data_len = lean_sarray_size(data);

        // Nothing to take, so nothing the state below could object to. A transport pump emitting a
        // zero-length read has not done anything wrong.
        if (data_len == 0) {
            return lean_io_result_mk_ok(lean_box(0));
        }

        if (ssl_obj->input_eof) {
            return mk_ssl_invalid_argument("the encrypted input stream was already ended by feedEof");
        }

        if (ssl_obj->err.failed) {
            return mk_ssl_session_dead(&ssl_obj->err);
        }

        // Once the peer's `close_notify` has arrived OpenSSL short-circuits every read, so nothing
        // will ever consume these bytes. Reporting success for them would let a transport pump grow
        // the BIO without bound while the caller is told the data was accepted. The peer chose to
        // send them, so this is a protocol fault rather than a caller error.
        if (peer_closed(ssl_obj->ssl)) {
            return mk_ssl_protocol_error("the peer already closed the TLS session");
        }

        if (data_len > ssl_max_io_bytes) {
            return mk_ssl_invalid_argument("the encrypted data to feed is too large");
        }

        BIO* rbio = SSL_get_rbio(ssl_obj->ssl);

        // Encrypted input the caller has not read back is what a peer can grow, so it is refused
        // until `read` gets back under the bound — the mirror of the output backlog on `write`.
        if (BIO_ctrl_pending(rbio) >= ssl_max_unread_encrypted_bytes) {
            return mk_ssl_input_backlog_full();
        }
        // A memory BIO takes the whole buffer or nothing, so a positive return is always `data_len`
        // and there is no partial write for the caller to resume from.
        int rc = BIO_write(rbio, lean_sarray_cptr(data), (int)data_len);
        if (rc > 0) {
            return lean_io_result_mk_ok(lean_box(0));
        }

        if (rc == 0) {
            return mk_ssl_internal_error("BIO_write: wrote 0 bytes");
        }

        if (BIO_should_retry(rbio)) {
            return mk_ssl_internal_error("BIO_write: unexpected retry flag on memory BIO");
        }

        return mk_ssl_internal_error("BIO_write failed");
    });
}

/* Std.Internal.SSL.Session.feedEof (ssl : @& Session) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_feed_eof(b_obj_arg ssl) {
    return ssl_entry_point([&] {
        lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);

        BIO_set_mem_eof_return(SSL_get_rbio(ssl_obj->ssl), 0);
        ssl_obj->input_eof = true;

        return lean_io_result_mk_ok(lean_box(0));
    });
}

/* Std.Internal.SSL.Session.drainEncrypted (ssl : @& Session) : IO ByteArray */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_drain_encrypted(b_obj_arg ssl) {
    return ssl_entry_point([&] {
        lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
        BIO* write_bio = SSL_get_wbio(ssl_obj->ssl);
        size_t pending = BIO_ctrl_pending(write_bio);

        if (pending == 0) {
            return lean_io_result_mk_ok(lean_mk_empty_byte_array(lean_box(0)));
        }

        if (pending > ssl_max_io_bytes) {
            return mk_ssl_internal_error("BIO_pending output too large");
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

        return mk_ssl_internal_error("BIO_read failed");
    });
}

/* Std.Internal.SSL.Session.pendingEncrypted (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_encrypted(b_obj_arg ssl) {
    return ssl_entry_point([&] {
        lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
        size_t pending = BIO_ctrl_pending(SSL_get_wbio(ssl_obj->ssl));
        return lean_io_result_mk_ok(lean_box_uint64((uint64_t)pending));
    });
}

/* Std.Internal.SSL.Session.pendingEncryptedInput (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_encrypted_input(b_obj_arg ssl) {
    return ssl_entry_point([&] {
        lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
        size_t pending = BIO_ctrl_pending(SSL_get_rbio(ssl_obj->ssl));
        return lean_io_result_mk_ok(lean_box_uint64((uint64_t)pending));
    });
}

/* Std.Internal.SSL.Session.pendingPlaintext (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_plaintext(b_obj_arg ssl) {
    return ssl_entry_point([&] {
        lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);

        int pending = SSL_pending(ssl_obj->ssl);
        return lean_io_result_mk_ok(lean_box_uint64(pending > 0 ? (uint64_t)pending : 0));
    });
}

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
        return mk_step_done();
    }

    if (rc == 0) {
        return nullptr;
    }

    int err = SSL_get_error(obj->ssl, rc);
    if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE) {
        if (lean_obj_res rejected = reject_want_write(obj, err)) {
            return rejected;
        }

        return mk_step_want_read();
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

    lean_obj_res diagnosis =
        mk_ssl_error_of(obj->ssl, &obj->err, err, sys_errno, reason, "could not shut down the TLS session");

    if (obj->err.failed) {
        release_pending_writes(obj);
    }

    return diagnosis;
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
        if (lean_obj_res rejected = reject_want_write(obj, flushed.err)) {
            return rejected;
        }

        return mk_step_want_read();
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
    return mk_step_want_read();
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
        return mk_step_done();
    }

    if (peer_closed(obj->ssl)) {
        return mk_step_done();
    }

    // The peek pulled in the start of another post-handshake message; the shutdown below would
    // refuse to run until the rest of it arrives.
    if (SSL_in_init(obj->ssl)) {
        return mk_step_want_read();
    }

    return nullptr;
}

/* Std.Internal.SSL.Session.closeNotify (ssl : @& Session) : IO Bool */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_close_notify(b_obj_arg ssl) {
    return ssl_entry_point([&] {
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
            return mk_step_done();
        }

        if (lean_obj_res r = close_notify_await_peer(obj)) {
            return r;
        }

        if (lean_obj_res done = close_notify_shutdown(obj)) {
            return done;
        }

        return mk_step_want_read();
    });
}

/* Std.Internal.SSL.Session.negotiatedVersion (ssl : @& Session) : IO String */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_negotiated_version(b_obj_arg ssl) {
    return ssl_entry_point([&] {
        lean_ssl_session_object* ssl_obj = lean_to_ssl_session_object(ssl);
        const char* version = SSL_get_version(ssl_obj->ssl);
        return lean_io_result_mk_ok(lean_mk_string(version != nullptr ? version : "unknown"));
    });
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

/* Std.Internal.SSL.Session.peerNameImpl (ssl : @& Session) : IO (Option String) */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_peer_name(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.handshake (ssl : @& Session) : IO Bool */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_handshake(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.write (ssl : @& Session) (data : @& ByteArray) : IO Bool */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_write(b_obj_arg /*ssl*/, b_obj_arg /*data*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.read (ssl : @& Session) (maxBytes : UInt64) : IO ReadResult */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_read(b_obj_arg /*ssl*/, uint64_t /*max_bytes*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.peek (ssl : @& Session) : IO ReadResult */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_peek(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.feedEncrypted (ssl : @& Session) (data : @& ByteArray) : IO Unit */
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

/* Std.Internal.SSL.Session.pendingEncryptedInput (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_encrypted_input(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.pendingPlaintext (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_plaintext(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.closeNotify (ssl : @& Session) : IO Bool */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_close_notify(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

/* Std.Internal.SSL.Session.negotiatedVersion (ssl : @& Session) : IO String */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_negotiated_version(b_obj_arg /*ssl*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

#endif

}
