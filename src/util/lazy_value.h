/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "util/thread.h"
#include <functional>

namespace lean {

template <class T>
class lazy_value {
    bool m_nonempty = false;
    mutex m_mutex;
    optional<T> m_value;
    std::exception_ptr m_ex;
    std::function<T()> m_closure;

    T const & get() {
        lean_assert(m_nonempty);
        unique_lock<mutex> _(m_mutex);
        if (m_value) return *m_value;
        if (m_ex) std::rethrow_exception(m_ex);
        try {
            m_value = { m_closure() };
            m_closure = {};
            return *m_value;
        } catch (...) {
            m_ex = std::current_exception();
            m_closure = {};
            throw;
        }
    }

public:
    lazy_value() {}
    lazy_value(std::function<T()> && closure) : m_nonempty(true), m_closure(closure) {}
    lazy_value(lazy_value const & other) { *this = other; }

    lazy_value & operator=(lazy_value const & other) {
        unique_lock<mutex> _(const_cast<lazy_value &>(other).m_mutex);
        m_nonempty = other.m_nonempty;
        m_value = other.m_value;
        m_ex = other.m_ex;
        m_closure = other.m_closure;
        return *this;
    }

    operator bool() const { return m_nonempty; }

    T const & operator*() const {
        return const_cast<lazy_value *>(this)->get();
    }
};

}
