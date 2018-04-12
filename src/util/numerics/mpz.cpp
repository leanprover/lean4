/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include "util/sstream.h"
#include "util/thread.h"
#include "util/numerics/mpz.h"
#include <string>

namespace lean {
mpz::mpz(uint64 v):
    mpz(static_cast<unsigned>(v)) {
    mpz tmp(static_cast<unsigned>(v >> 32));
    mpz_mul_2exp(tmp.m_val, tmp.m_val, 32);
    mpz_add(m_val, m_val, tmp.m_val);
}

unsigned mpz::log2() const {
    if (is_nonpos())
        return 0;
    unsigned r = mpz_sizeinbase(m_val, 2);
    lean_assert(r > 0);
    return r - 1;
}

unsigned mpz::mlog2() const {
    if (is_nonneg())
        return 0;
    mpz * _this = const_cast<mpz*>(this);
    _this->neg();
    lean_assert(is_pos());
    unsigned r = mpz_sizeinbase(m_val, 2);
    _this->neg();
    lean_assert(is_neg());
    return r - 1;
}

bool mpz::is_power_of_two(unsigned & shift) const {
    if (is_nonpos())
        return false;
    if (mpz_popcount(m_val) == 1) {
        shift = log2();
        return true;
    } else {
        return false;
    }
}

mpz operator%(mpz const & a, mpz const & b) {
    mpz r(rem(a, b));
    if (r.is_neg()) {
        if (b.is_pos())
            r += b;
        else
            r -= b;
    }
    return r;
}

bool root(mpz & root, mpz const & a, unsigned k) {
    mpz rem;
    mpz_rootrem(root.m_val, rem.m_val, a.m_val, k);
    return rem.is_zero();
}

void display(std::ostream & out, __mpz_struct const * v) {
    size_t sz = mpz_sizeinbase(v, 10) + 2;
    if (sz < 1024) {
        char buffer[1024];
        mpz_get_str(buffer, 10, v);
        out << buffer;
    } else {
        std::unique_ptr<char> buffer(new char[sz]);
        mpz_get_str(buffer.get(), 10, v);
        out << buffer.get();
    }
}

std::ostream & operator<<(std::ostream & out, mpz const & v) {
    display(out, v.m_val);
    return out;
}

std::string mpz::to_string() const {
    std::ostringstream out;
    out << *this;
    return out.str();
}

serializer & operator<<(serializer & s, mpz const & n) {
    std::ostringstream out;
    out << n;
    s << out.str();
    return s;
}

mpz read_mpz(deserializer & d) {
    return mpz(d.read_string().c_str());
}
}

void print(lean::mpz const & n) { std::cout << n << std::endl; }
