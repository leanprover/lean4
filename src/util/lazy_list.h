/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/debug.h"
#include "util/rc.h"
#include "util/optional.h"

namespace lean {
/**
   \brief ML-like lazy lists.
*/
template<typename T>
class lazy_list {
public:
    typedef optional<std::pair<T, lazy_list>> maybe_pair; // head and tail pair
private:
    class cell_base {
        MK_LEAN_RC();
        void dealloc() { delete this; }
    public:
        cell_base():m_rc(0) {}
        virtual ~cell_base() {}
        virtual maybe_pair pull() const = 0;
    };

    template<typename F>
    class cell : public cell_base {
        F m_f;
    public:
        cell(F && f):cell_base(), m_f(f) {}
        virtual ~cell() {}
        virtual maybe_pair pull() const { return m_f(); }
    };

    cell_base * m_ptr;
public:
    lazy_list():m_ptr(nullptr) {}
    lazy_list(lazy_list const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    lazy_list(lazy_list && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    template<typename F> explicit lazy_list(F && f):m_ptr(new cell<F>(std::forward<F>(f))) { m_ptr->inc_ref(); }
    ~lazy_list() { if (m_ptr) m_ptr->dec_ref(); }

    lazy_list & operator=(lazy_list const & s) { LEAN_COPY_REF(lazy_list, s); }
    lazy_list & operator=(lazy_list && s) { LEAN_MOVE_REF(lazy_list, s); }

    maybe_pair pull() const {
        if (m_ptr)
            return m_ptr->pull();
        else
            return maybe_pair();
    }

    friend T head(lazy_list const & l) { return l.pull()->first; }
    friend lazy_list tail(lazy_list const & l) { return l.pull()->second; }
};
}
