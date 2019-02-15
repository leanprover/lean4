/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/object_ref.h"

namespace lean {
/* Wrapper for manipulating Lean runtime nat values in C++. */
class nat : public object_ref {
    static nat wrap(object * o) { return nat(o, true); }
public:
    nat():object_ref(box(0)) {}
    explicit nat(obj_arg o):object_ref(o) {}
    nat(b_obj_arg o, bool b):object_ref(o, b) {}
    explicit nat(int v):object_ref(mk_nat_obj(v < 0 ? 0u : static_cast<unsigned>(v))) {}
    explicit nat(unsigned v):object_ref(mk_nat_obj(v)) {}
    explicit nat(mpz const & v):object_ref(mk_nat_obj(v)) {}
    explicit nat(char const * v):object_ref(box(0)) {
        mpz m(v);
        if (m > 0)
            *this = nat(mk_nat_obj(m));
    }
    nat(nat const & other):object_ref(other) {}
    nat(nat && other):object_ref(other) {}

    nat & operator=(nat const & other) { object_ref::operator=(other); return *this; }
    nat & operator=(nat && other) { object_ref::operator=(other); return *this; }

    bool is_small() const { return is_scalar(raw()); }
    unsigned get_small_value() const { lean_assert(is_small()); return unbox(raw()); }
    mpz const & get_big_value() const { lean_assert(!is_small()); return mpz_value(raw()); }
    mpz to_mpz() const { return is_small() ? mpz(unbox(raw())) : mpz_value(raw()); }
    std::string to_std_string() const { return to_mpz().to_string(); }
    static unsigned hash(object * o) { return is_scalar(o) ? unbox(o) : mpz_value(o).hash(); }
    unsigned hash() const { return hash(raw()); }
    friend bool operator==(nat const & a, nat const & b) { return nat_eq(a.raw(), b.raw()); }
    friend bool operator!=(nat const & a, nat const & b) { return !(a == b); }
    friend bool operator<=(nat const & a, nat const & b) { return nat_le(a.raw(), b.raw()); }
    friend bool operator<(nat const & a,  nat const & b) { return nat_lt(a.raw(), b.raw()); }
    friend bool operator>=(nat const & a, nat const & b) { return b <= a; }
    friend bool operator>(nat const & a,  nat const & b) { return b < a; }
    friend bool operator==(nat const & a, unsigned b)    { return a == nat(b); }
    friend bool operator!=(nat const & a, unsigned b)    { return !(a == b); }
    friend bool operator<=(nat const & a, unsigned b)    { return a <= nat(b); }
    friend bool operator<(nat const & a,  unsigned b)    { return a < nat(b); }
    friend bool operator>=(nat const & a, unsigned b)    { return a >= nat(b); }
    friend bool operator>(nat const & a,  unsigned b)    { return a > nat(b); }
    friend nat operator+(nat const & a, nat const & b)   { return wrap(nat_add(a.raw(), b.raw())); }
    friend nat operator-(nat const & a, nat const & b)   { return wrap(nat_sub(a.raw(), b.raw())); }
    friend nat operator*(nat const & a, nat const & b)   { return wrap(nat_mul(a.raw(), b.raw())); }
    friend nat operator/(nat const & a, nat const & b)   { return wrap(nat_div(a.raw(), b.raw())); }
    friend nat operator%(nat const & a, nat const & b)   { return wrap(nat_mod(a.raw(), b.raw())); }
    void serialize(serializer & s) const { s.write_object(raw()); }
    static nat deserialize(deserializer & d) { return nat(d.read_object(), true); }
};

inline optional<nat> to_optional_nat(obj_arg o) {
    if (is_scalar(o)) return optional<nat>();
    optional<nat> r(nat(cnstr_get(o, 0), true));
    dec(o);
    return r;
}

inline serializer & operator<<(serializer & s, nat const & n) { n.serialize(s); return s; }
inline nat read_nat(deserializer & d) { return nat::deserialize(d); }
inline deserializer & operator>>(deserializer & d, nat & n) { n = read_nat(d); return d; }
inline std::ostream & operator<<(std::ostream & out, nat const & n) { out << n.to_mpz(); return out; }
};
