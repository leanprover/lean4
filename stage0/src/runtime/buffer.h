/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <cstring>
#include "runtime/debug.h"
#include "runtime/optional.h"

namespace lean {
/**
    \brief Very similar to std::vector, but stores elements on the
    system stack when collection has less than \c INITIAL_SIZE.
    This collection is useful when writing functions that need
    temporary storage.
*/
template<typename T, size_t INITIAL_SIZE = 16>
class buffer {
protected:
    T *      m_buffer;
    size_t   m_pos;
    size_t   m_capacity;
    char     m_initial_buffer[INITIAL_SIZE * sizeof(T)];

    void free_memory() {
        if (m_buffer != reinterpret_cast<T*>(m_initial_buffer))
            #if __cpp_sized_deallocation >= 201309L
                operator delete[](reinterpret_cast<char*>(m_buffer), sizeof(T) * m_capacity);
            #else
                delete[] reinterpret_cast<char*>(m_buffer);
            #endif
    }

    void set_capacity(size_t new_capacity) {
        lean_assert(new_capacity > m_capacity);
        char * new_buffer_char = new char[sizeof(T) * new_capacity];
        T * new_buffer         = reinterpret_cast<T*>(new_buffer_char);
        std::uninitialized_copy(m_buffer, m_buffer + m_pos, new_buffer);
        destroy();
        m_buffer              = new_buffer;
        m_capacity            = new_capacity;
    }

    void expand() {
        set_capacity(m_capacity << 1);
    }

    void destroy_elements() {
        std::for_each(begin(), end(), [](T & e) { e.~T(); });
    }

    void destroy() {
        destroy_elements();
        free_memory();
    }

public:
    typedef T value_type;
    typedef T * iterator;
    typedef T const * const_iterator;

    buffer():
        m_buffer(reinterpret_cast<T *>(m_initial_buffer)),
        m_pos(0),
        m_capacity(INITIAL_SIZE) {
    }

    buffer(buffer const & source):
        m_buffer(reinterpret_cast<T *>(m_initial_buffer)),
        m_pos(0),
        m_capacity(INITIAL_SIZE) {
        std::for_each(source.begin(), source.end(), [=](T const & e) { push_back(e); });
    }

    void ensure_capacity(size_t new_capacity) {
        if (new_capacity > m_capacity) {
            set_capacity(new_capacity);
        }
    }

    ~buffer() { destroy(); }

    buffer & operator=(buffer const & source) {
        clear();
        std::for_each(source.begin(), source.end(), [=](T const & e) { push_back(e); });
        return *this;
    }

    bool operator==(buffer const & other) const {
        if (size() != other.size()) {
            return false;
        } else {
            for (size_t i = 0; i < size(); i++) {
                if (operator[](i) != other[i])
                    return false;
            }
            return true;
        }
    }

    bool operator!=(buffer const & other) const {
        return !operator==(other);
    }

    T const & back() const { lean_assert(!empty() && m_pos > 0); return m_buffer[m_pos - 1]; }
    T & back() { lean_assert(!empty() && m_pos > 0); return m_buffer[m_pos - 1]; }
    T & operator[](size_t idx) { lean_assert(idx < size());  return m_buffer[idx]; }
    T const & operator[](size_t idx) const { lean_assert(idx < size()); return m_buffer[idx]; }
    void clear() { destroy_elements(); m_pos = 0; }
    size_t size() const { return m_pos; }
    T const * data() const { return m_buffer; }
    T * data() { return m_buffer; }
    bool empty() const { return m_pos == 0;  }
    iterator begin() { return m_buffer; }
    iterator end() { return m_buffer + size(); }
    const_iterator begin() const { return m_buffer; }
    const_iterator end() const { return m_buffer + size(); }
    size_t capacity() const { return m_capacity; }

    void push_back(T const & elem) {
        if (m_pos >= m_capacity)
            expand();
        new (m_buffer + m_pos) T(elem);
        m_pos++;
    }

    template<typename... Args>
    void emplace_back(Args&&... args) {
        if (m_pos >= m_capacity)
            expand();
        new (m_buffer + m_pos) T(args...);
        m_pos++;
    }

    void pop_back() {
        back().~T();
        m_pos--;
    }

    void append(size_t sz, T const * elems) {
        ensure_capacity(size() + sz);
        for (size_t i = 0; i < sz; i++)
            push_back(elems[i]);
    }

    template<typename C>
    void append(C const & c) {
        append(c.size(), c.data());
    }

    void resize(size_t nsz, T const & elem = T()) {
        size_t sz = size();
        if (nsz > sz) {
            ensure_capacity(nsz);
            for (size_t i = sz; i < nsz; i++)
                push_back(elem);
        } else if (nsz < sz) {
            for (size_t i = nsz; i < sz; i++)
                pop_back();
        }
        lean_assert(size() == nsz);
    }

    void erase(size_t idx) {
        lean_assert(idx < size());
        for (size_t i = idx+1; i < size(); i++)
            m_buffer[i-1] = std::move(m_buffer[i]);
        pop_back();
    }

    void erase_elem(T const & elem) {
        for (size_t i = 0; i < size(); i++) {
            if (m_buffer[i] == elem) {
                erase(i);
                return;
            }
        }
    }

    optional<size_t> index_of(T const & elem) const {
        for (size_t i = 0; i < size(); i++)
            if (m_buffer[i] == elem) return optional<size_t>(i);
        return optional<size_t>();
    }

    void insert(size_t idx, T const & elem) {
        using std::swap;
        lean_assert(idx <= size());
        push_back(elem);
        size_t i = size();
        while (i > idx + 1) {
            --i;
            swap(m_buffer[i], m_buffer[i-1]);
        }
    }

    void shrink(size_t nsz) {
        size_t sz = size();
        lean_assert(nsz <= sz);
        for (size_t i = nsz; i < sz; i++)
            pop_back();
        lean_assert(size() == nsz);
    }
};

}
