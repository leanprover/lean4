/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits.h>
#include "util/thread.h"
#include "util/numerics/mpbq.h"

namespace lean {
MK_THREAD_LOCAL_GET_DEF(mpz, get_tlocal1);
MK_THREAD_LOCAL_GET_DEF(mpz, get_tlocal2);
bool set(mpbq & a, mpq const & b) {
    if (b.is_integer()) {
        numerator(a.m_num, b);
        a.m_k = 0;
        return true;
    } else {
        mpz & d = get_tlocal1();
        denominator(d, b);
        unsigned shift;
        if (d.is_power_of_two(shift)) {
            numerator(a.m_num, b);
            a.m_k = shift;
            lean_assert(a == b);
            return true;
        } else {
            numerator(a.m_num, b);
            a.m_k = d.log2() + 1;
            return false;
        }
    }
}

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
    mpz & tmp = get_tlocal1();
    if (a.m_k == b.m_k) {
        return cmp(a.m_num, b.m_num);
    } else if (a.m_k < b.m_k) {
        mul2k(tmp, a.m_num, b.m_k - a.m_k);
        return cmp(tmp, b.m_num);
    } else {
        lean_assert(a.m_k > b.m_k);
        mul2k(tmp, b.m_num, a.m_k - b.m_k);
        return cmp(a.m_num, tmp);
    }
}

int cmp(mpbq const & a, mpz const & b) {
    mpz & tmp = get_tlocal1();
    if (a.m_k == 0) {
        return cmp(a.m_num, b);
    } else {
        mul2k(tmp, b, a.m_k);
        return cmp(a.m_num, tmp);
    }
}

int cmp(mpbq const & a, mpq const & b) {
    if (a.is_integer() && b.is_integer()) {
        return -cmp(b, a.m_num);
    } else {
        mpz & tmp1 = get_tlocal1();
        mpz & tmp2 = get_tlocal2();
        // tmp1 <- numerator(a)*denominator(b)
        denominator(tmp1, b); tmp1 *= a.m_num;
        // tmp2 <- numerator(b)*denominator(a)
        numerator(tmp2, b); mul2k(tmp2, tmp2, a.m_k);
        return cmp(tmp1, tmp2);
    }
}

mpbq & mpbq::operator+=(mpbq const & a) {
    if (m_k == a.m_k) {
        m_num += a.m_num;
    } else if (m_k < a.m_k) {
        mul2k(m_num, m_num, a.m_k - m_k);
        m_k    = a.m_k;
        m_num += a.m_num;
    } else {
        lean_assert(m_k > a.m_k);
        mpz & tmp = get_tlocal1();
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
    } else {
        lean_assert(m_k > 0);
        mpz & tmp = get_tlocal1();
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
    } else if (m_k < a.m_k) {
        mul2k(m_num, m_num, a.m_k - m_k);
        m_k    = a.m_k;
        m_num -= a.m_num;
    } else {
        lean_assert(m_k > a.m_k);
        mpz & tmp = get_tlocal1();
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
    } else {
        lean_assert(m_k > 0);
        mpz & tmp = get_tlocal1();
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
    } else {
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

void power(mpbq & a, mpbq const & b, unsigned k) {
    lean_assert(static_cast<unsigned long long>(k) * static_cast<unsigned long long>(b.m_k) <= static_cast<unsigned long long>(UINT_MAX));
    // We don't need to normalize because:
    //   If b.m_k == 0, then b is an integer, and the result be an integer
    //   If b.m_k > 0, then b.m_num must be odd, and the (b.m_num)^k will also be odd
    a.m_k = b.m_k * k;
    power(a.m_num, b.m_num, k);
}

int mpbq::magnitude_lb() const {
    int s = m_num.sgn();
    if (s < 0) {
        return m_num.mlog2() - m_k + 1;
    } else if (s == 0) {
        return 0;
    } else {
        lean_assert(s > 0);
        return m_num.log2() - m_k;
    }
}

int mpbq::magnitude_ub() const {
    int s = m_num.sgn();
    if (s < 0) {
        return m_num.mlog2() - m_k;
    } else if (s == 0) {
        return 0;
    } else {
        lean_assert(s > 0);
        return m_num.log2() - m_k + 1;
    }
}

void mul2(mpbq & a) {
    if (a.m_k == 0) {
        mul2k(a.m_num, a.m_num, 1);
    } else {
        a.m_k--;
    }
}

void mul2k(mpbq & a, unsigned k) {
    if (k == 0)
        return;
    if (a.m_k < k) {
        mul2k(a.m_num, a.m_num, k - a.m_k);
        a.m_k = 0;
    } else {
        lean_assert(a.m_k >= k);
        a.m_k -= k;
    }
}

bool root_lower(mpbq & a, mpbq const & b, unsigned n) {
    bool r = root(a.m_num, b.m_num, n);
    if (!r)
        --a.m_num;
    if (b.m_k % n == 0) {
        a.m_k = b.m_k / n;
        a.normalize();
        return r;
    } else if (a.m_num.is_neg()) {
        a.m_k = b.m_k / n;
        a.normalize();
        return false;
    } else {
        a.m_k = b.m_k / n;
        a.m_k++;
        a.normalize();
        return false;
    }
}

bool root_upper(mpbq & a, mpbq const & b, unsigned n) {
    bool r = root(a.m_num, b.m_num, n);
    if (b.m_k % n == 0) {
        a.m_k = b.m_k / n;
        a.normalize();
        return r;
    } else if (a.m_num.is_neg()) {
        a.m_k = b.m_k / n;
        a.m_k++;
        a.normalize();
        return false;
    } else {
        a.m_k = b.m_k / n;
        a.normalize();
        return false;
    }
}

void refine_upper(mpq const & q, mpbq & l, mpbq & u) {
    lean_assert(l < q && q < u);
    lean_assert(!q.get_denominator().is_power_of_two());
    mpbq mid;
    while (true) {
        mid = l + u;
        div2(mid);
        if (mid > q) {
            swap(u, mid);
            lean_assert(l < q && q < u);
            return;
        }
        swap(l, mid);
    }
}

void refine_lower(mpq const & q, mpbq & l, mpbq & u) {
    lean_assert(l < q && q < u);
    lean_assert(!q.get_denominator().is_power_of_two());
    mpbq mid;
    while (true) {
        mid = l + u;
        div2(mid);
        if (mid < q) {
            swap(l, mid);
            lean_assert(l < q && q < u);
            return;
        }
        swap(u, mid);
    }
}

bool lt_1div2k(mpbq const & a, unsigned k) {
    if (a.m_num.is_nonpos())
        return true;
    if (a.m_k <= k) {
        // since a.m_num >= 1
        return false;
    } else {
        lean_assert(a.m_k > k);
        mpz & tmp = get_tlocal1();
        tmp = 1;
        mul2k(tmp, tmp, a.m_k - k);
        return a.m_num < tmp;
    }
}

std::ostream & operator<<(std::ostream & out, mpbq const & v) {
    if (v.m_k == 0) {
        out << v.m_num;
    } else if (v.m_k == 1) {
        out << v.m_num << "/2";
    } else {
        out << v.m_num << "/2^" << v.m_k;
    }
    return out;
}

void display_decimal(std::ostream & out, mpbq const & a, unsigned prec) {
    if (a.is_integer()) {
        out << a.m_num;
        return;
    } else {
        mpz two_k;
        mpz n1, v1;
        if (a.is_neg())
            out << "-";
        v1 = abs(a.m_num);
        power(two_k, mpz(2), a.m_k);
        n1 = rem(v1, two_k);
        v1 = v1/two_k;
        lean_assert(!n1.is_zero());
        out << v1;
        out << ".";
        for (unsigned i = 0; i < prec; i++) {
            n1 *= 10;
            v1  = n1/two_k;
            n1  = rem(n1, two_k);
            out << v1;
            if (n1.is_zero())
                return;
        }
        out << "?";
    }
}

MK_THREAD_LOCAL_GET(bool, get_rnd, false);

bool & numeric_traits<mpbq>::get_rnd() {
    return ::lean::get_rnd();
}

static mpbq * g_zero = nullptr;
mpbq const & numeric_traits<mpbq>::zero() {
    lean_assert(is_zero(*g_zero));
    return *g_zero;
}

void initialize_mpbq() {
    g_zero = new mpbq();
}
void finalize_mpbq() {
    delete g_zero;
}
}

void print(lean::mpbq const & n) { std::cout << n << std::endl; }
