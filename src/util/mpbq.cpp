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
    div2k(m_num, m_num, k);
    m_k -= k;
}

int cmp(mpbq const & a, mpbq const & b) {
    static thread_local mpz tmp;
    if (a.m_k == b.m_k)
        return cmp(a.m_num, b.m_num);
    else if (a.m_k < b.m_k) {
        mul2k(tmp, a.m_num, b.m_k - a.m_k);
        return cmp(tmp, b.m_num);
    }
    else {
        lean_assert(a.m_k > b.m_k);
        mul2k(tmp, b.m_num, a.m_k - b.m_k);
        return cmp(a.m_num, tmp);
    }
}

int cmp(mpbq const & a, mpz const & b) {
    static thread_local mpz tmp;
    if (a.m_k == 0)
        return cmp(a.m_num, b);
    else {
        mul2k(tmp, b, a.m_k);
        return cmp(a.m_num, tmp);
    }
}

mpbq & mpbq::operator+=(mpbq const & a) {
    if (m_k == a.m_k) {
        m_num += a.m_num;
    }
    else if (m_k < a.m_k) {
        mul2k(m_num, m_num, a.m_k - m_k);
        m_k    = a.m_k;
        m_num += a.m_num;
    }
    else {
        lean_assert(m_k > a.m_k);
        static thread_local mpz tmp;
        mul2k(tmp, a.m_num, m_k - a.m_k);
        m_num += tmp;
    }
    normalize();
    return *this;
}

template<typename T> 
mpbq & mpbq::add_int(T const & a) {
    if (m_k == 0) {
        m_num += a;
    }
    else {
        lean_assert(m_k > 0);
        static thread_local mpz tmp;
        tmp = a;
        mul2k(tmp, tmp, m_k);
        m_num += tmp;
    }
    normalize();
    return *this;
}    
mpbq & mpbq::operator+=(unsigned a) { return add_int<unsigned>(a); }
mpbq & mpbq::operator+=(int a) { return add_int<int>(a); }

mpbq & mpbq::operator-=(mpbq const & a) {
    if (m_k == a.m_k) {
        m_num -= a.m_num;
    }
    else if (m_k < a.m_k) {
        mul2k(m_num, m_num, a.m_k - m_k);
        m_k    = a.m_k;
        m_num -= a.m_num;
    }
    else {
        lean_assert(m_k > a.m_k);
        static thread_local mpz tmp;
        mul2k(tmp, a.m_num, m_k - a.m_k);
        m_num -= tmp;
    }
    normalize();
    return *this;
}

template<typename T> 
mpbq & mpbq::sub_int(T const & a) {
    if (m_k == 0) {
        m_num -= a;
    }
    else {
        lean_assert(m_k > 0);
        static thread_local mpz tmp;
        tmp = a;
        mul2k(tmp, tmp, m_k);
        m_num -= tmp;
    }
    normalize();
    return *this;
}    
mpbq & mpbq::operator-=(unsigned a) { return sub_int<unsigned>(a); }
mpbq & mpbq::operator-=(int a) { return sub_int<int>(a); }

mpbq & mpbq::operator*=(mpbq const & a) {
    m_num *= a.m_num;
    if (m_k == 0 || a.m_k == 0) {
        m_k   += a.m_k;
        normalize();
    }
    else {
        m_k   += a.m_k;
    }
    return *this;
}

template<typename T> 
mpbq & mpbq::mul_int(T const & a) {
    m_num *= a;
    normalize();
    return *this;
}    
mpbq & mpbq::operator*=(unsigned a) { return mul_int<unsigned>(a); }
mpbq & mpbq::operator*=(int a) { return mul_int<int>(a); }

int mpbq::magnitude_lb() const {
    int s = m_num.sgn();
    if (s < 0) {
        return m_num.mlog2() - m_k + 1;
    }
    else if (s == 0) {
        return 0;
    }
    else {
        lean_assert(s > 0);
        return m_num.log2() - m_k;
    }
}

int mpbq::magnitude_ub() const {
    int s = m_num.sgn();
    if (s < 0) {
        return m_num.mlog2() - m_k;
    }
    else if (s == 0) {
        return 0;
    }
    else {
        lean_assert(s > 0);
        return m_num.log2() - m_k + 1;
    }
}

void mul2(mpbq & a) {
    if (a.m_k == 0) {
        mul2k(a.m_num, a.m_num, 1);
    }
    else {
        a.m_k--;
    }
}

void mul2k(mpbq & a, unsigned k) {
    if (k == 0)
        return;
    if (a.m_k < k) {
        mul2k(a.m_num, a.m_num, k - a.m_k);
        a.m_k = 0;
    }
    else {
        lean_assert(a.m_k >= k);
        a.m_k -= k;
    }
}

std::ostream & operator<<(std::ostream & out, mpbq const & v) {
    if (v.m_k == 0) {
        out << v.m_num;
    }
    else if (v.m_k == 1) {
        out << v.m_num << "/2";
    }
    else {
        out << v.m_num << "/2^" << v.m_k;
    }
    return out;
}

}

void pp(lean::mpbq const & n) { std::cout << n << std::endl; }
