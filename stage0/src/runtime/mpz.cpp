/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <string>
#include "runtime/sstream.h"
#include "runtime/thread.h"
#include "runtime/mpz.h"

namespace lean {
mpz::mpz(uint64 v):
    mpz(static_cast<unsigned>(v)) {
    mpz tmp(static_cast<unsigned>(v >> 32));
    mpz_mul_2exp(tmp.m_val, tmp.m_val, 32);
    mpz_add(m_val, m_val, tmp.m_val);
}

mpz::mpz(int64 v) {
    uint64 w;
    if (v < 0) w = -v;
    else w = v;
    mpz_init_set_ui(m_val, static_cast<unsigned>(w));
    mpz tmp(static_cast<unsigned>(w >> 32));
    mpz_mul_2exp(tmp.m_val, tmp.m_val, 32);
    mpz_add(m_val, m_val, tmp.m_val);
    if (v < 0)
        mpz_neg(m_val, m_val);
}

size_t mpz::get_size_t() const {
    // GMP only features accessors up to `unsigned long`, which is smaller than `size_t` on Windows.
    // So we directly access the lowest mpz word instead.
    static_assert(sizeof(size_t) == sizeof(mp_limb_t), "GMP word size should be equal system word size");
    // NOTE: mpz_getlimbn returns 0 if the index is out of range (i.e. `m_val == 0`)
    return static_cast<size_t>(mpz_getlimbn(m_val, 0));
}

size_t mpz::log2() const {
    if (is_nonpos())
        return 0;
    size_t r = mpz_sizeinbase(m_val, 2);
    lean_assert(r > 0);
    return r - 1;
}

mpz operator%(mpz const & a, mpz const & b) {
    return rem(a, b);
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
}

void print(lean::mpz const & n) { std::cout << n << std::endl; }
