/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"

#define LEAN_VM_MAX_SMALL_INT (1 << 30)
#define LEAN_VM_MIN_SMALL_INT -(1 << 30)

namespace lean {
// =======================================
// Builtin int operations
inline bool is_small_int(int n)         { return LEAN_VM_MIN_SMALL_INT <= n && n < LEAN_VM_MAX_SMALL_INT; }
inline bool is_small_int(unsigned n)    { return n < LEAN_VM_MAX_SMALL_INT; }
inline bool is_small_int(long long n)   { return LEAN_VM_MIN_SMALL_INT <= n && n < LEAN_VM_MAX_SMALL_INT; }
inline bool is_small_int(mpz const & n) { return LEAN_VM_MIN_SMALL_INT <= n && n < LEAN_VM_MAX_SMALL_INT; }

inline unsigned to_unsigned(int n) {
    lean_assert(is_small_int(n));
    unsigned r = static_cast<unsigned>(n) & 0x7FFFFFFF;
    lean_assert(r < LEAN_VM_MAX_SMALL_NAT);
    return r;
}

inline  int of_unsigned(unsigned n) {
    return static_cast<int>(n << 1) / 2;
}

vm_obj mk_vm_int(int n) {
    return is_small_int(n) ? mk_vm_simple(to_unsigned(n)) : mk_vm_mpz(mpz(n));
}

vm_obj mk_vm_int(unsigned n) {
    return is_small_int(n) ? mk_vm_simple(to_unsigned(n)) : mk_vm_mpz(mpz(n));
}

vm_obj mk_vm_int(mpz const & n) {
    return is_small_int(n) ? mk_vm_simple(to_unsigned(n.get_int())) : mk_vm_mpz(n);
}

inline int to_small_int(vm_obj const & o) {
    lean_assert(is_simple(o));
    return of_unsigned(cidx(o));
}

int to_int(vm_obj const & o) {
    if (is_simple(o))
        return to_small_int(o);
    else
        return to_mpz(o).get_int();
}

optional<int> try_to_int(vm_obj const & o) {
    if (is_simple(o)) {
        return optional<int>(to_small_int(o));
    } else {
        mpz const & v = to_mpz(o);
        if (v.is_int())
            return optional<int>(v.get_int());
        else
            return optional<int>();
    }
}

int force_to_int(vm_obj const & o, int def) {
    if (auto r = try_to_int(o))
        return *r;
    else
        return def;
}

MK_THREAD_LOCAL_GET_DEF(mpz, get_mpz1);
MK_THREAD_LOCAL_GET_DEF(mpz, get_mpz2);

static mpz const & to_mpz1(vm_obj const & o) {
    if (is_simple(o)) {
        mpz & r = get_mpz1();
        r = to_small_int(o);
        return r;
    } else {
        return to_mpz(o);
    }
}

static mpz const & to_mpz2(vm_obj const & o) {
    if (is_simple(o)) {
        mpz & r = get_mpz2();
        r = to_small_int(o);
        return r;
    } else {
        return to_mpz(o);
    }
}

vm_obj int_add(vm_obj const & a1, vm_obj const & a2) {
    if (is_simple(a1) && is_simple(a2)) {
        return mk_vm_int(to_small_int(a1) + to_small_int(a2));
    } else {
        return mk_vm_int(to_mpz1(a1) + to_mpz2(a2));
    }
}

vm_obj int_sub(vm_obj const & a1, vm_obj const & a2) {
    if (is_simple(a1) && is_simple(a2)) {
        return mk_vm_int(to_small_int(a1) - to_small_int(a2));
    } else {
        return mk_vm_int(to_mpz1(a1) - to_mpz2(a2));
    }
}

vm_obj int_mul(vm_obj const & a1, vm_obj const & a2) {
    if (is_simple(a1) && is_simple(a2)) {
        long long r = static_cast<long long>(to_small_int(a1)) * static_cast<long long>(to_small_int(a2));
        if (is_small_int(r)) {
            return mk_vm_simple(to_unsigned(r));
        }
    }
    return mk_vm_int(to_mpz1(a1) * to_mpz2(a2));
}

vm_obj int_div(vm_obj const & a1, vm_obj const & a2) {
    if (is_simple(a1) && is_simple(a2)) {
        int v1 = to_small_int(a1);
        int v2 = to_small_int(a2);
        if (v2 == 0)
            return mk_vm_simple(0);
        else
            return mk_vm_int(v1 / v2);
    } else {
        mpz const & v1 = to_mpz1(a1);
        mpz const & v2 = to_mpz2(a2);
        if (v2 == 0)
            return mk_vm_simple(0);
        else
            return mk_vm_int(v1 / v2);
    }
}

vm_obj int_mod(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
        int v1 = to_small_int(a1);
        int v2 = to_small_int(a2);
        if (v2 == 0)
            return a1;
        else
            return mk_vm_int(v1 % v2);
    } else {
        mpz const & v1 = to_mpz1(a1);
        mpz const & v2 = to_mpz2(a2);
        if (v2 == 0)
            return a1;
        else
            return mk_vm_int(rem(v1, v2));
    }
}

vm_obj int_gcd(vm_obj const & a1, vm_obj const & a2) {
    mpz r;
    gcd(r, to_mpz1(a1), to_mpz2(a2));
    return mk_vm_nat(r);
}

vm_obj int_decidable_eq(vm_obj const & a1, vm_obj const & a2) {
    if (is_simple(a1) && is_simple(a2)) {
        return mk_vm_bool(to_small_int(a1) == to_small_int(a2));
    } else {
        return mk_vm_bool(to_mpz1(a1) == to_mpz2(a2));
    }
}

vm_obj int_decidable_le(vm_obj const & a1, vm_obj const & a2) {
    if (is_simple(a1) && is_simple(a2)) {
        return mk_vm_bool(to_small_int(a1) <= to_small_int(a2));
    } else {
        return mk_vm_bool(to_mpz1(a1) <= to_mpz2(a2));
    }
}

vm_obj int_decidable_lt(vm_obj const & a1, vm_obj const & a2) {
    if (is_simple(a1) && is_simple(a2)) {
        return mk_vm_bool(to_small_int(a1) < to_small_int(a2));
    } else {
        return mk_vm_bool(to_mpz1(a1) < to_mpz2(a2));
    }
}

vm_obj int_neg(vm_obj const & a) {
    if (is_simple(a)) {
        return mk_vm_int(-to_small_int(a));
    } else {
        return mk_vm_int(0 - to_mpz1(a));
    }
}

vm_obj int_nat_abs(vm_obj const & a) {
    if (is_simple(a)) {
        int n = to_small_int(a);
        return mk_vm_nat(n < 0 ? -n : n);
    } else {
        mpz z = to_mpz1(a);
        return mk_vm_nat(z < 0 ? (0 - z) : z);
    }
}

vm_obj int_of_nat(vm_obj const & a) {
    if (is_simple(a)) {
        return mk_vm_int(cidx(a));
    } else {
        return a;
    }
}

vm_obj int_neg_succ_of_nat(vm_obj const & a) {
    if (is_simple(a)) {
        return mk_vm_int(-static_cast<int>(cidx(a)) - 1);
    } else {
        return mk_vm_int(0 - to_mpz1(a) - 1);
    }
}

void initialize_vm_int() {
    DECLARE_VM_BUILTIN(name({"int", "of_nat"}),           int_of_nat);
    DECLARE_VM_BUILTIN(name({"int", "nat_abs"}),          int_nat_abs);
    DECLARE_VM_BUILTIN(name({"int", "neg_succ_of_nat"}),  int_neg_succ_of_nat);
    DECLARE_VM_BUILTIN(name({"int", "add"}),              int_add);
    DECLARE_VM_BUILTIN(name({"int", "sub"}),              int_sub);
    DECLARE_VM_BUILTIN(name({"int", "mul"}),              int_mul);
    DECLARE_VM_BUILTIN(name({"int", "neg"}),              int_neg);
    DECLARE_VM_BUILTIN(name({"int", "div"}),              int_div);
    DECLARE_VM_BUILTIN(name({"int", "mod"}),              int_mod);
    DECLARE_VM_BUILTIN(name({"int", "dec_eq"}),           int_decidable_eq);
    DECLARE_VM_BUILTIN(name({"int", "dec_le"}),           int_decidable_le);
    DECLARE_VM_BUILTIN(name({"int", "dec_lt"}),           int_decidable_lt);
}

void finalize_vm_int() {
}
}
