/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <algorithm>
#include "util/rc.h"

namespace lean {

class power : public pair<unsigned, unsigned> {
public:
    typedef unsigned var;
    power(var v, unsigned d):pair<var, unsigned>(v, d) {}
    var get_var() const { return first; }
    void set_var(var x) { first = x; }
    unsigned degree() const { return second; }
    unsigned & degree() { return second; }
    struct lt_var {
        bool operator()(power const & p1, power const & p2) const { return p1.get_var() < p2.get_var(); }
    };
    struct lt_degree {
        bool operator()(power const & p1, power const & p2) const { return p1.degree() < p2.degree(); }
    };
};

template<typename T>
class monomial {
    struct cell {
        MK_LEAN_RC();
        unsigned m_total_degree;
        unsigned m_size;
        unsigned m_hash;
        power    m_powers[0];
    };
    cell * m_ptr;
public:
    monomial():m_ptr(nullptr) {}
    monomial(monomial const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    monomial(monomial && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~monomial() { if (m_ptr) m_ptr->dec_ref(); }

    static monomial const & null();

    friend void swap(monomial & a, monomial & b) { std::swap(a.m_ptr, b.m_ptr); }

    void release() { if (m_ptr) m_ptr->dec_ref(); m_ptr = nullptr; }

    monomial & operator=(monomial const & s) { LEAN_COPY_REF(s); }
    monomial & operator=(monomial && s) { LEAN_MOVE_REF(s); }
};

template<typename T>
class polynomial {
    struct cell {
        MK_LEAN_RC();
        unsigned m_size:31;
        unsigned m_lex_sorted:1;
        T *        m_as;
        monomial * m_ms;
    };
    cell * m_ptr;
public:
    polynomial():m_ptr(nullptr) {}
    polynomial(polynomial const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    polynomial(polynomial && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~polynomial() { if (m_ptr) m_ptr->dec_ref(); }

    static polynomial const & null();

    friend void swap(polynomial & a, polynomial & b) { std::swap(a.m_ptr, b.m_ptr); }

    void release() { if (m_ptr) m_ptr->dec_ref(); m_ptr = nullptr; }

    polynomial & operator=(polynomial const & s) { LEAN_COPY_REF(s); }
    polynomial & operator=(polynomial && s) { LEAN_MOVE_REF(s); }
};
}
