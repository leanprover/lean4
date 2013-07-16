/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved. 
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura 
*/
#include "mpq.h"

namespace lean {

void mpq::floor() {
    if (is_integer())
        return;
    bool neg = is_neg();
    mpz_tdiv_q(mpq_numref(m_val), mpq_numref(m_val), mpq_denref(m_val));
    mpz_set_ui(mpq_denref(m_val), 1);
    if (neg)
        mpz_sub_ui(mpq_numref(m_val), mpq_numref(m_val), 1);
}

void mpq::ceil() {
    if (is_integer())
        return;
    bool pos = is_pos();
    mpz_tdiv_q(mpq_numref(m_val), mpq_numref(m_val), mpq_denref(m_val));
    mpz_set_ui(mpq_denref(m_val), 1);
    if (pos)
        mpz_add_ui(mpq_numref(m_val), mpq_numref(m_val), 1);
}

mpz floor(mpq const & a) {
    if (a.is_integer())
        return a.get_numerator();
    mpz r;
    mpz_tdiv_q(mpq::zval(r), mpq_numref(a.m_val), mpq_denref(a.m_val));
    if (a.is_neg())
        r -= 1;
    return r;
}

mpz ceil(mpq const & a) {
    if (a.is_integer())
        return a.get_numerator();
    mpz r;
    mpz_tdiv_q(mpq::zval(r), mpq_numref(a.m_val), mpq_denref(a.m_val));
    if (a.is_pos())
        r += 1;
    return r;
}

extern void display(std::ostream & out, __mpz_struct const * v);

std::ostream & operator<<(std::ostream & out, mpq const & v) {
    if (v.is_integer()) {
        display(out, mpq_numref(v.m_val));
    }
    else {
        display(out, mpq_numref(v.m_val));
        out << "/";
        display(out, mpq_denref(v.m_val));
    }
    return out;
}

void pp(mpq const & v) { std::cout << v << std::endl; }

}
