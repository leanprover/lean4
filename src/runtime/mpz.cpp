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

mpz::mpz() {
    mpz_init(m_val);
}

mpz::mpz(mpz_t v) {
    mpz_init(m_val);
    mpz_set(m_val, v);
}

mpz::mpz(char const * v) {
    mpz_init_set_str(m_val, const_cast<char*>(v), 10);
}

mpz::mpz(unsigned int v) {
    mpz_init_set_ui(m_val, v);
}

mpz::mpz(int v) {
    mpz_init_set_si(m_val, v);
}

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

mpz::mpz(mpz const & s) {
    mpz_init_set(m_val, s.m_val);
}

mpz::mpz(mpz && s):mpz() {
    mpz_swap(m_val, s.m_val);
}

mpz::~mpz() {
    mpz_clear(m_val);
}

void mpz::set(mpz_t r) const {
    mpz_set(r, m_val);
}

void swap(mpz & a, mpz & b) {
    mpz_swap(a.m_val, b.m_val);
}

bool mpz::is_int() const {
    return mpz_fits_sint_p(m_val) != 0;
}

bool mpz::is_unsigned_int() const {
    return mpz_fits_uint_p(m_val) != 0;
}

bool mpz::is_long_int() const {
    return mpz_fits_slong_p(m_val) != 0;
}

bool mpz::is_unsigned_long_int() const {
    return mpz_fits_ulong_p(m_val) != 0;
}

bool mpz::is_size_t() const {
    // GMP only features `fits` functions up to `unsigned long`, which is smaller than `size_t` on Windows.
    // So we directly count the number of mpz words instead.
    static_assert(sizeof(size_t) == sizeof(mp_limb_t), "GMP word size should be equal to system word size");
    return is_nonneg() && mpz_size(m_val) <= 1;
}

long int mpz::get_long_int() const {
    lean_assert(is_long_int()); return mpz_get_si(m_val);
}

int mpz::get_int() const {
    lean_assert(is_int()); return static_cast<int>(get_long_int());
}

unsigned long int mpz::get_unsigned_long_int() const {
    lean_assert(is_unsigned_long_int()); return mpz_get_ui(m_val);
}

unsigned int mpz::get_unsigned_int() const {
    lean_assert(is_unsigned_int()); return static_cast<unsigned>(get_unsigned_long_int());
}

size_t mpz::get_size_t() const {
    // GMP only features accessors up to `unsigned long`, which is smaller than `size_t` on Windows.
    // So we directly access the lowest mpz word instead.
    static_assert(sizeof(size_t) == sizeof(mp_limb_t), "GMP word size should be equal system word size");
    // NOTE: mpz_getlimbn returns 0 if the index is out of range (i.e. `m_val == 0`)
    return static_cast<size_t>(mpz_getlimbn(m_val, 0));
}

mpz & mpz::operator=(mpz const & v) {
    mpz_set(m_val, v.m_val); return *this;
}

mpz & mpz::operator=(char const * v) {
    mpz_set_str(m_val, v, 10); return *this;
}

mpz & mpz::operator=(unsigned int v) {
    mpz_set_ui(m_val, v); return *this;
}

mpz & mpz::operator=(int v) {
    mpz_set_si(m_val, v); return *this;
}

int cmp(mpz const & a, mpz const & b) {
    return mpz_cmp(a.m_val, b.m_val);
}

int cmp(mpz const & a, unsigned b) {
    return mpz_cmp_ui(a.m_val, b);
}

int cmp(mpz const & a, unsigned long b) {
    return mpz_cmp_ui(a.m_val, b);
}

int cmp(mpz const & a, int b) {
    return mpz_cmp_si(a.m_val, b);
}

mpz & mpz::operator+=(mpz const & o) { mpz_add(m_val, m_val, o.m_val); return *this; }

mpz & mpz::operator+=(unsigned u) { mpz_add_ui(m_val, m_val, u); return *this; }

mpz & mpz::operator+=(int u) { if (u >= 0) mpz_add_ui(m_val, m_val, u); else mpz_sub_ui(m_val, m_val, -u); return *this; }

mpz & mpz::operator-=(mpz const & o) { mpz_sub(m_val, m_val, o.m_val); return *this; }

mpz & mpz::operator-=(unsigned u) { mpz_sub_ui(m_val, m_val, u); return *this; }

mpz & mpz::operator-=(int u) { if (u >= 0) mpz_sub_ui(m_val, m_val, u); else mpz_add_ui(m_val, m_val, -u); return *this; }

mpz & mpz::operator*=(mpz const & o) { mpz_mul(m_val, m_val, o.m_val); return *this; }

mpz & mpz::operator*=(unsigned u) { mpz_mul_ui(m_val, m_val, u); return *this; }

mpz & mpz::operator*=(int u) { mpz_mul_si(m_val, m_val, u); return *this; }

mpz & mpz::operator/=(mpz const & o) { mpz_tdiv_q(m_val, m_val, o.m_val); return *this; }
mpz & mpz::operator/=(unsigned u) { mpz_tdiv_q_ui(m_val, m_val, u); return *this; }

mpz rem(mpz const & a, mpz const & b) { mpz r; mpz_tdiv_r(r.m_val, a.m_val, b.m_val); return r; }

mpz mpz::pow(unsigned int exp) const {
    mpz r;
    mpz_pow_ui(r.m_val, m_val, exp);
    return r;
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

mpz & mpz::operator&=(mpz const & o) {
    mpz_and(m_val, m_val, o.m_val);
    return *this;
}

mpz & mpz::operator|=(mpz const & o) {
    mpz_ior(m_val, m_val, o.m_val);
    return *this;
}

mpz & mpz::operator^=(mpz const & o) {
    mpz_xor(m_val, m_val, o.m_val);
    return *this;
}

void mul2k(mpz & a, mpz const & b, unsigned k) {
    mpz_mul_2exp(a.m_val, b.m_val, k);
}

void div2k(mpz & a, mpz const & b, unsigned k) {
    mpz_tdiv_q_2exp(a.m_val, b.m_val, k);
}

void mod2k(mpz & a, mpz const & b, unsigned k) {
    mpz_tdiv_r_2exp(a.m_val, b.m_val, k);
}

void power(mpz & a, mpz const & b, unsigned k) {
    mpz_pow_ui(a.m_val, b.m_val, k);
}

void gcd(mpz & g, mpz const & a, mpz const & b) {
    mpz_gcd(g.m_val, a.m_val, b.m_val);
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
