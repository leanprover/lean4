/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved. 
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura 
*/
#include "mpbq.h"

namespace lean {

void mpbq::normalize() {
    if (m_k == 0)
        return;
    if (is_zero()) {
        m_k = 0;
        return;
    }

    unsigned k = m_num.power_of_two_multiple();
    if (k > m_k)
        k = m_k;
    m_num.div2k(k);
    m_k -= k;
}


int cmp(mpbq const & a, mpbq const & b) {
    if (a.m_k == b.m_k)
        return cmp(a.m_num, b.m_num);
    else if (a.m_k < b.m_k) {
        mpz tmp(a.m_num);
        tmp.mul2k(b.m_k - a.m_k);
        return cmp(tmp, b.m_num);
    }
    else {
        lean_assert(a.m_k > b.m_k);
        mpz tmp(b.m_num);
        tmp.mul2k(a.m_k - b.m_k);
        return cmp(a.m_num, tmp);
    }
}

int cmp(mpbq const & a, mpz const & b) {
    if (a.m_k == 0)
        return cmp(a.m_num, b);
    else {
        mpz tmp(b);
        tmp.mul2k(a.m_k);
        return cmp(a.m_num, tmp);
    }
}


}

