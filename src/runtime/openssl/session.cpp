/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/session.h"

#include <climits>
#include <cstdlib>
#include <cstring>
#include <string>

#ifndef LEAN_EMSCRIPTEN
#include <openssl/err.h>
#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

static inline lean_object * mk_ssl_error(char const * where, int ssl_err = 0) {
    unsigned long err = ERR_get_error();
    char err_buf[256];
    err_buf[0] = '\0';

    if (err != 0) {
        ERR_error_string_n(err, err_buf, sizeof(err_buf));
    }

    // Drain remaining errors so they don't pollute future calls.
    ERR_clear_error();

    std::string msg(where);
    
    if (ssl_err != 0) {
        msg += " (ssl_error=" + std::to_string(ssl_err) + ")";
    }
    if (err_buf[0] != '\0') {
        msg += ": ";
        msg += err_buf;
    }

    return lean_mk_io_user_error(mk_string(msg.c_str()));
}

static inline lean_obj_res mk_ssl_io_error(char const * where, int ssl_err = 0) {
    return lean_io_result_mk_error(mk_ssl_error(where, ssl_err));
}

static inline lean_object * mk_empty_byte_array() {
    lean_object * arr = lean_alloc_sarray(1, 0, 0);
    lean_sarray_set_size(arr, 0);
    return arr;
}

static void free_pending_writes(lean_ssl_session_object * obj) {
    if (obj->pending_writes != nullptr) {
        for (size_t i = 0; i < obj->pending_writes_count; i++) {
            free(obj->pending_writes[i].data);
        }
        free(obj->pending_writes);
        obj->pending_writes = nullptr;
    }
    obj->pending_writes_count = 0;
}

static bool append_pending_write(lean_ssl_session_object * obj, char const * data, size_t size) {
    char * copy = (char*)malloc(size);
    if (copy == nullptr) return false;

    std::memcpy(copy, data, size);

    size_t new_count = obj->pending_writes_count + 1;
    lean_ssl_pending_write * new_arr = (lean_ssl_pending_write*)realloc(
        obj->pending_writes, sizeof(lean_ssl_pending_write) * new_count
    );

    if (new_arr == nullptr) {
        free(copy);
        return false;
    }

    obj->pending_writes = new_arr;
    obj->pending_writes[obj->pending_writes_count].data = copy;
    obj->pending_writes[obj->pending_writes_count].size = size;
    obj->pending_writes_count = new_count;
    return true;
}

/*
Return values:
  1 -> write completed
  0 -> write blocked (WANT_READ / WANT_WRITE / ZERO_RETURN)
 -1 -> fatal error
*/
static int ssl_write_step(lean_ssl_session_object * obj, char const * data, size_t size, int * out_err) {
    if (size > INT_MAX) {
        *out_err = SSL_ERROR_SSL;
        return -1;
    }

    int rc = SSL_write(obj->ssl, data, (int)size);
    if (rc > 0) {
        return 1;
    }

    int err = SSL_get_error(obj->ssl, rc);
    *out_err = err;
    if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE || err == SSL_ERROR_ZERO_RETURN) {
        return 0;
    }
    return -1;
}

/*
Return values:
  1 -> all pending writes flushed
  0 -> still blocked by renegotiation
 -1 -> fatal error, *out_err filled
*/
static int try_flush_pending_writes(lean_ssl_session_object * obj, int * out_err) {
    if (obj->pending_writes_count == 0) return 1;

    size_t completed = 0;

    for (size_t i = 0; i < obj->pending_writes_count; i++) {
        lean_ssl_pending_write * pw = &obj->pending_writes[i];

        while (pw->size > 0) {
            int err = 0;
            int step = ssl_write_step(obj, pw->data, pw->size, &err);

            if (step == 1) {
                // We do not enable partial writes, so a successful SSL_write consumes the full buffer.
                pw->size = 0;
                continue;
            }

            if (step == 0) {
                goto done;
            }

            *out_err = err;
            return -1;
        }

        free(pw->data);
        pw->data = nullptr;
        completed++;
    }

done:
    if (completed > 0) {
        obj->pending_writes_count -= completed;
        if (obj->pending_writes_count == 0) {
            free(obj->pending_writes);
            obj->pending_writes = nullptr;
        } else {
            std::memmove(
                obj->pending_writes,
                obj->pending_writes + completed,
                sizeof(lean_ssl_pending_write) * obj->pending_writes_count
            );
            // Keep memory usage proportional to currently queued writes.
            lean_ssl_pending_write * shrunk = (lean_ssl_pending_write*)realloc(
                obj->pending_writes,
                sizeof(lean_ssl_pending_write) * obj->pending_writes_count
            );
            if (shrunk != nullptr) {
                obj->pending_writes = shrunk;
            }
        }
    }

    return obj->pending_writes_count == 0 ? 1 : 0;
}

void lean_ssl_session_finalizer(void * ptr) {
    lean_ssl_session_object * obj = (lean_ssl_session_object*)ptr;

    if (obj->ssl != nullptr) {
        SSL_free(obj->ssl);
    }

    free_pending_writes(obj);
    free(obj);
}

void initialize_openssl_session() {
    g_ssl_session_external_class = lean_register_external_class(lean_ssl_session_finalizer, [](void * obj, lean_object * f) {
        (void)obj;
        (void)f;
    });
}

static lean_obj_res mk_ssl_session(uint8_t is_server) {
    SSL_CTX * ctx = is_server ? get_openssl_server_ctx() : get_openssl_client_ctx();
    if (ctx == nullptr) {
        return mk_ssl_io_error("failed to initialize OpenSSL context");
    }

    SSL * ssl = SSL_new(ctx);
    if (ssl == nullptr) {
        return mk_ssl_io_error("SSL_new failed");
    }

    BIO * read_bio = BIO_new(BIO_s_mem());
    BIO * write_bio = BIO_new(BIO_s_mem());

    if (read_bio == nullptr || write_bio == nullptr) {
        if (read_bio != nullptr) BIO_free(read_bio);
        if (write_bio != nullptr) BIO_free(write_bio);
        SSL_free(ssl);
        return mk_ssl_io_error("BIO_new failed");
    }

    BIO_set_nbio(read_bio, 1);
    BIO_set_nbio(write_bio, 1);

    SSL_set_bio(ssl, read_bio, write_bio);
    SSL_set_mode(ssl, SSL_MODE_AUTO_RETRY);

    if (is_server) {
        SSL_set_accept_state(ssl);
    } else {
        SSL_set_connect_state(ssl);
    }

    lean_ssl_session_object * ssl_obj = (lean_ssl_session_object*)malloc(sizeof(lean_ssl_session_object));
    if (ssl_obj == nullptr) {
        SSL_free(ssl);
        return mk_ssl_io_error("failed to allocate SSL session object");
    }

    ssl_obj->ssl = ssl;
    ssl_obj->read_bio = read_bio;
    ssl_obj->write_bio = write_bio;
    ssl_obj->pending_writes_count = 0;
    ssl_obj->pending_writes = nullptr;

    lean_object * obj = lean_ssl_session_object_new(ssl_obj);
    lean_mark_mt(obj);
    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.SSL.Session.mk (isServer : Bool) : IO Session */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_mk(uint8_t is_server) {
    return mk_ssl_session(is_server);
}

/* Std.Internal.SSL.Session.mkServer : IO Session */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_mk_server() {
    return mk_ssl_session(1);
}

/* Std.Internal.SSL.Session.mkClient : IO Session */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_mk_client() {
    return mk_ssl_session(0);
}

/* Std.Internal.SSL.configureServerContext (certFile keyFile : @& String) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_configure_server_ctx(b_obj_arg cert_file, b_obj_arg key_file) {
    SSL_CTX * ctx = get_openssl_server_ctx();
    if (ctx == nullptr) {
        return mk_ssl_io_error("failed to initialize OpenSSL context");
    }

    const char * cert = lean_string_cstr(cert_file);
    const char * key = lean_string_cstr(key_file);

    if (SSL_CTX_use_certificate_file(ctx, cert, SSL_FILETYPE_PEM) <= 0) {
        return mk_ssl_io_error("SSL_CTX_use_certificate_file failed");
    }

    if (SSL_CTX_use_PrivateKey_file(ctx, key, SSL_FILETYPE_PEM) <= 0) {
        return mk_ssl_io_error("SSL_CTX_use_PrivateKey_file failed");
    }

    if (SSL_CTX_check_private_key(ctx) != 1) {
        return mk_ssl_io_error("SSL_CTX_check_private_key failed");
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.SSL.configureClientContext (caFile : @& String) (verifyPeer : Bool) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_configure_client_ctx(b_obj_arg ca_file, uint8_t verify_peer) {
    SSL_CTX * ctx = get_openssl_client_ctx();
    if (ctx == nullptr) {
        return mk_ssl_io_error("failed to initialize OpenSSL client context");
    }

    const char * ca = lean_string_cstr(ca_file);
    if (ca != nullptr && ca[0] != '\0') {
        if (SSL_CTX_load_verify_locations(ctx, ca, nullptr) != 1) {
            return mk_ssl_io_error("SSL_CTX_load_verify_locations failed");
        }
    } else if (verify_peer) {
        // Fall back to platform trust anchors when no custom CA file is provided.
        if (SSL_CTX_set_default_verify_paths(ctx) != 1) {
            return mk_ssl_io_error("SSL_CTX_set_default_verify_paths failed");
        }
    }

    SSL_CTX_set_verify(ctx, verify_peer ? SSL_VERIFY_PEER : SSL_VERIFY_NONE, nullptr);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.SSL.Session.setServerName (ssl : @& Session) (host : @& String) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_set_server_name(b_obj_arg ssl, b_obj_arg host) {
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    const char * server_name = lean_string_cstr(host);
    if (SSL_set_tlsext_host_name(ssl_obj->ssl, server_name) != 1) {
        return mk_ssl_io_error("SSL_set_tlsext_host_name failed");
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.SSL.Session.verifyResult (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_verify_result(b_obj_arg ssl) {
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    long result = SSL_get_verify_result(ssl_obj->ssl);
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)result));
}

/* Std.Internal.SSL.Session.handshake (ssl : @& Session) : IO Bool */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_handshake(b_obj_arg ssl) {
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    int rc = SSL_do_handshake(ssl_obj->ssl);

    if (rc == 1) {
        return lean_io_result_mk_ok(lean_box(1));
    }

    int err = SSL_get_error(ssl_obj->ssl, rc);
    if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE || err == SSL_ERROR_ZERO_RETURN) {
        return lean_io_result_mk_ok(lean_box(0));
    }

    return mk_ssl_io_error("SSL_do_handshake failed", err);
}

/* Std.Internal.SSL.Session.write (ssl : @& Session) (data : @& ByteArray) : IO Bool */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_write(b_obj_arg ssl, b_obj_arg data) {
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    size_t data_len = lean_sarray_size(data);
    char const * payload = (char const*)lean_sarray_cptr(data);

    if (data_len == 0) {
        return lean_io_result_mk_ok(lean_box(1));
    }

    int err = 0;
    int step = ssl_write_step(ssl_obj, payload, data_len, &err);
    if (step == 1) {
        return lean_io_result_mk_ok(lean_box(1));
    }

    // If renegotiation blocks writes, queue plaintext and retry after subsequent reads.
    if (step == 0 && err == SSL_ERROR_WANT_READ) {
        if (!append_pending_write(ssl_obj, payload, data_len)) {
            return mk_ssl_io_error("failed to append pending SSL write");
        }
        return lean_io_result_mk_ok(lean_box(0));
    }

    if (step == 0 && (err == SSL_ERROR_WANT_WRITE || err == SSL_ERROR_ZERO_RETURN)) {
        return lean_io_result_mk_ok(lean_box(0));
    }

    return mk_ssl_io_error("SSL_write failed", err);
}

/* Std.Internal.SSL.Session.read? (ssl : @& Session) (maxBytes : UInt64) : IO (Option ByteArray) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_read(b_obj_arg ssl, uint64_t max_bytes) {
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);

    if (max_bytes == 0) {
        return lean_io_result_mk_ok(mk_option_some(mk_empty_byte_array()));
    }

    if (max_bytes > INT_MAX) {
        max_bytes = INT_MAX;
    }

    lean_object * out = lean_alloc_sarray(1, 0, max_bytes);
    int rc = SSL_read(ssl_obj->ssl, (void*)lean_sarray_cptr(out), (int)max_bytes);

    if (rc > 0) {
        int flush_err = 0;
        if (try_flush_pending_writes(ssl_obj, &flush_err) < 0) {
            lean_dec(out);
            return mk_ssl_io_error("pending SSL write flush failed", flush_err);
        }
        lean_sarray_set_size(out, (size_t)rc);
        return lean_io_result_mk_ok(mk_option_some(out));
    }

    lean_dec(out);

    int err = SSL_get_error(ssl_obj->ssl, rc);
    if (err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE || err == SSL_ERROR_ZERO_RETURN) {
        int flush_err = 0;
        if (try_flush_pending_writes(ssl_obj, &flush_err) < 0) {
            return mk_ssl_io_error("pending SSL write flush failed", flush_err);
        }
        return lean_io_result_mk_ok(mk_option_none());
    }

    return mk_ssl_io_error("SSL_read failed", err);
}

/* Std.Internal.SSL.Session.feedEncrypted (ssl : @& Session) (data : @& ByteArray) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_feed_encrypted(b_obj_arg ssl, b_obj_arg data) {
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    size_t data_len = lean_sarray_size(data);

    if (data_len == 0) {
        return lean_io_result_mk_ok(lean_box_uint64(0));
    }

    if (data_len > INT_MAX) {
        return mk_ssl_io_error("BIO_write input too large");
    }

    int rc = BIO_write(ssl_obj->read_bio, lean_sarray_cptr(data), (int)data_len);
    if (rc >= 0) {
        return lean_io_result_mk_ok(lean_box_uint64((uint64_t)rc));
    }

    if (BIO_should_retry(ssl_obj->read_bio)) {
        return lean_io_result_mk_ok(lean_box_uint64(0));
    }

    return mk_ssl_io_error("BIO_write failed");
}

/* Std.Internal.SSL.Session.drainEncrypted (ssl : @& Session) : IO ByteArray */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_drain_encrypted(b_obj_arg ssl) {
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    size_t pending = BIO_ctrl_pending(ssl_obj->write_bio);

    if (pending == 0) {
        return lean_io_result_mk_ok(mk_empty_byte_array());
    }

    if (pending > INT_MAX) {
        return mk_ssl_io_error("BIO_pending output too large");
    }

    lean_object * out = lean_alloc_sarray(1, 0, pending);
    int rc = BIO_read(ssl_obj->write_bio, (void*)lean_sarray_cptr(out), (int)pending);

    if (rc >= 0) {
        lean_sarray_set_size(out, (size_t)rc);
        return lean_io_result_mk_ok(out);
    }

    lean_dec(out);

    if (BIO_should_retry(ssl_obj->write_bio)) {
        return lean_io_result_mk_ok(mk_empty_byte_array());
    }

    return mk_ssl_io_error("BIO_read failed");
}

/* Std.Internal.SSL.Session.pendingEncrypted (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_pending_encrypted(b_obj_arg ssl) {
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)BIO_ctrl_pending(ssl_obj->write_bio)));
}

/* Std.Internal.SSL.Session.pendingPlaintext (ssl : @& Session) : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_pending_plaintext(b_obj_arg ssl) {
    lean_ssl_session_object * ssl_obj = lean_to_ssl_session_object(ssl);
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)SSL_pending(ssl_obj->ssl)));
}

#else

void initialize_openssl_session() {}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_mk(uint8_t is_server) {
    (void)is_server;
    return io_result_mk_error("lean_uv_ssl_mk is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_configure_server_ctx(b_obj_arg cert_file, b_obj_arg key_file) {
    (void)cert_file;
    (void)key_file;
    return io_result_mk_error("lean_uv_ssl_configure_server_ctx is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_configure_client_ctx(b_obj_arg ca_file, uint8_t verify_peer) {
    (void)ca_file;
    (void)verify_peer;
    return io_result_mk_error("lean_uv_ssl_configure_client_ctx is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_set_server_name(b_obj_arg ssl, b_obj_arg host) {
    (void)ssl;
    (void)host;
    return io_result_mk_error("lean_uv_ssl_set_server_name is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_verify_result(b_obj_arg ssl) {
    (void)ssl;
    return io_result_mk_error("lean_uv_ssl_verify_result is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_mk_server() {
    return io_result_mk_error("lean_uv_ssl_mk_server is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_mk_client() {
    return io_result_mk_error("lean_uv_ssl_mk_client is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_handshake(b_obj_arg ssl) {
    (void)ssl;
    return io_result_mk_error("lean_uv_ssl_handshake is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_write(b_obj_arg ssl, b_obj_arg data) {
    (void)ssl;
    (void)data;
    return io_result_mk_error("lean_uv_ssl_write is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_read(b_obj_arg ssl, uint64_t max_bytes) {
    (void)ssl;
    (void)max_bytes;
    return io_result_mk_error("lean_uv_ssl_read is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_feed_encrypted(b_obj_arg ssl, b_obj_arg data) {
    (void)ssl;
    (void)data;
    return io_result_mk_error("lean_uv_ssl_feed_encrypted is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_drain_encrypted(b_obj_arg ssl) {
    (void)ssl;
    return io_result_mk_error("lean_uv_ssl_drain_encrypted is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_pending_encrypted(b_obj_arg ssl) {
    (void)ssl;
    return io_result_mk_error("lean_uv_ssl_pending_encrypted is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_pending_plaintext(b_obj_arg ssl) {
    (void)ssl;
    return io_result_mk_error("lean_uv_ssl_pending_plaintext is not supported");
}

#endif

}
