/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include <cerrno>
#include <cstring>

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#include <memory>
#include <new>
#endif

namespace lean {

// `nullptr` if `size` is a valid receive buffer size. libuv reports an empty buffer as `UV_ENOBUFS`,
// which would read as a resource shortage.
inline lean_obj_res recv_size_error(uint64_t size) {
    if (size != 0) {
        return nullptr;
    }

    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, lean_mk_string("receive buffer size must be positive")));
}

// Sets the size of a receive buffer to the `nread` bytes it received. A read that fills less than half
// of it is moved to a buffer of its own size instead, so that many small reads do not each keep a
// full-sized buffer alive.
inline lean_object * fit_read_buffer(lean_object * byte_array, size_t nread) {
    if (nread * 2 >= lean_sarray_capacity(byte_array)) {
        lean_sarray_set_size(byte_array, nread);
        return byte_array;
    }

    lean_object * fitted = lean_alloc_sarray(1, nread, nread);
    memcpy(lean_sarray_cptr(fitted), lean_sarray_cptr(byte_array), nread);
    lean_dec(byte_array);
    return fitted;
}

#ifndef LEAN_EMSCRIPTEN

// The `uv_buf_t` array for sending an `Array ByteArray`, on the stack unless it is large. `uv_write`
// and `uv_udp_send` copy the array before returning, so it only has to outlive that call. The bytes
// must outlive the request, so the request keeps the `Array ByteArray`.
class uv_send_bufs {
    static constexpr size_t inline_capacity = 16;

    uv_buf_t m_inline[inline_capacity];
    std::unique_ptr<uv_buf_t[]> m_heap;
    uv_buf_t * m_data = m_inline;
    unsigned int m_count = 0;

public:
    uv_send_bufs() = default;
    uv_send_bufs(uv_send_bufs const &) = delete;
    uv_send_bufs & operator=(uv_send_bufs const &) = delete;

    // Points the buffers at the bytes of `data_array`. `false` if allocating the array failed.
    [[nodiscard]] bool init(b_obj_arg data_array) {
        size_t len = lean_array_size(data_array);
        if (len > inline_capacity) {
            m_heap.reset(new (std::nothrow) uv_buf_t[len]);
            if (m_heap == nullptr) {
                return false;
            }
            m_data = m_heap.get();
        }

        for (size_t i = 0; i < len; i++) {
            lean_object * byte_array = lean_array_get_core(data_array, i);
            m_data[i] = uv_buf_init((char*)lean_sarray_cptr(byte_array), lean_sarray_size(byte_array));
        }

        m_count = len;
        return true;
    }

    uv_buf_t const * data() const { return m_data; }
    unsigned int count() const { return m_count; }
};

#endif

}
