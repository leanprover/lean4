/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <cstring>
#include "util/debug.h"
#include "util/optional.h"

namespace lean {
/**
    \brief Very similar to std::vector, but stores elements on the
    system stack when collection has less than \c INITIAL_SIZE.
    This collection is useful when writing functions that need
    temporary storage.
*/
template<typename T, unsigned INITIAL_SIZE = 16>
class buffer {
protected:
    T *      m_buffer;
    unsigned m_pos;
    unsigned m_capacity;
    char     m_initial_buffer[INITIAL_SIZE * sizeof(T)];

    void free_memory() {
        if (m_buffer != reinterpret_cast<T*>(m_initial_buffer))
            delete[] reinterpret_cast<char*>(m_buffer);
    }

    void expand() {
        unsigned new_capacity  = m_capacity << 1;
        char * new_buffer_char = new char[sizeof(T) * new_capacity];
        T * new_buffer         = reinterpret_cast<T*>(new_buffer_char);
        std::uninitialized_copy(m_buffer, m_buffer + m_pos, new_buffer);
        destroy();
        m_buffer              = new_buffer;
        m_capacity            = new_capacity;
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
            for (unsigned i = 0; i < size(); i++) {
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
    T & operator[](unsigned idx) { lean_assert(idx < size());  return m_buffer[idx]; }
    T const & operator[](unsigned idx) const { lean_assert(idx < size()); return m_buffer[idx]; }
    void clear() { destroy_elements(); m_pos = 0; }
    unsigned size() const { return m_pos; }
    T const * data() const { return m_buffer; }
    T * data() { return m_buffer; }
    bool empty() const { return m_pos == 0;  }
    iterator begin() { return m_buffer; }
    iterator end() { return m_buffer + size(); }
    const_iterator begin() const { return m_buffer; }
    const_iterator end() const { return m_buffer + size(); }
    unsigned capacity() const { return m_capacity; }

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

    void append(unsigned sz, T const * elems) {
        for (unsigned i = 0; i < sz; i++)
            push_back(elems[i]);
    }

    template<typename C>
    void append(C const & c) {
        append(c.size(), c.data());
    }

    void resize(unsigned nsz, T const & elem = T()) {
        unsigned sz = size();
        if (nsz > sz) {
            for (unsigned i = sz; i < nsz; i++)
                push_back(elem);
        } else if (nsz < sz) {
            for (unsigned i = nsz; i < sz; i++)
                pop_back();
        }
        lean_assert(size() == nsz);
    }

    void erase(unsigned idx) {
        lean_assert(idx < size());
        for (unsigned i = idx+1; i < size(); i++)
            m_buffer[i-1] = std::move(m_buffer[i]);
        pop_back();
    }

    void erase_elem(T const & elem) {
        for (unsigned i = 0; i < size(); i++) {
            if (m_buffer[i] == elem) {
                erase(i);
                return;
            }
        }
    }

    optional<unsigned> index_of(T const & elem) const {
        for (unsigned i = 0; i < size(); i++)
            if (m_buffer[i] == elem) return optional<unsigned>(i);
        return optional<unsigned>();
    }

    void insert(unsigned idx, T const & elem) {
        using std::swap;
        lean_assert(idx <= size());
        push_back(elem);
        unsigned i = size();
        while (i > idx + 1) {
            --i;
            swap(m_buffer[i], m_buffer[i-1]);
        }
    }

    void shrink(unsigned nsz) {
        unsigned sz = size();
        lean_assert(nsz <= sz);
        for (unsigned i = nsz; i < sz; i++)
            pop_back();
        lean_assert(size() == nsz);
    }
};

}
