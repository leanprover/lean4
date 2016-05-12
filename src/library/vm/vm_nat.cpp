/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constants.h"
#include "library/vm/vm.h"

namespace lean {
// =======================================
// Builtin nat operations
#define MAX_SMALL_NAT 1u<<31

vm_obj mk_vm_nat(unsigned n) {
    if (n < MAX_SMALL_NAT)
        return mk_vm_simple(n);
    else
        return mk_vm_mpz(mpz(n));
}

vm_obj mk_vm_nat(mpz const & n) {
    if (n < MAX_SMALL_NAT)
        return mk_vm_simple(n.get_unsigned_int());
    else
        return mk_vm_mpz(n);
}

MK_THREAD_LOCAL_GET_DEF(mpz, get_mpz1);
MK_THREAD_LOCAL_GET_DEF(mpz, get_mpz2);

static mpz const & to_mpz1(vm_obj const & o) {
    if (is_simple(o)) {
        mpz & r = get_mpz1();
        r = cidx(o);
        return r;
    } else {
        return to_mpz(o);
    }
}

static mpz const & to_mpz2(vm_obj const & o) {
    if (is_simple(o)) {
        mpz & r = get_mpz2();
        r = cidx(o);
        return r;
    } else {
        return to_mpz(o);
    }
}

static void nat_succ(vm_state & s) {
    vm_obj const & a = s.get(0);
    if (is_simple(a)) {
        s.push(mk_vm_nat(cidx(a) + 1));
    } else {
        s.push(mk_vm_mpz(to_mpz1(a) + 1));
    }
}

static void nat_add(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    if (is_simple(a1) && is_simple(a2)) {
        s.push(mk_vm_nat(cidx(a1) + cidx(a2)));
    } else {
        s.push(mk_vm_mpz(to_mpz1(a1) + to_mpz2(a2)));
    }
}

static void nat_mul(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    if (is_simple(a1) && is_simple(a2)) {
        unsigned long long r = static_cast<unsigned long long>(cidx(a1)) + static_cast<unsigned long long>(cidx(a2));
        if (r < MAX_SMALL_NAT) {
            s.push(mk_vm_simple(r));
            return;
        }
    }
    s.push(mk_vm_mpz(to_mpz1(a1) * to_mpz2(a2)));
}

static void nat_sub(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    if (is_simple(a1) && is_simple(a2)) {
        unsigned v1 = cidx(a1);
        unsigned v2 = cidx(a2);
        if (v2 > v1)
            s.push(mk_vm_simple(0));
        else
            s.push(mk_vm_nat(v1 - v2));
    } else {
        mpz const & v1 = to_mpz1(a1);
        mpz const & v2 = to_mpz2(a2);
        if (v2 > v1)
            s.push(mk_vm_simple(0));
        else
            s.push(mk_vm_nat(v1 - v2));
    }
}

static void nat_div(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    if (is_simple(a1) && is_simple(a2)) {
        unsigned v1 = cidx(a1);
        unsigned v2 = cidx(a2);
        if (v2 == 0)
            s.push(mk_vm_simple(0));
        else
            s.push(mk_vm_nat(v1 / v2));
    } else {
        mpz const & v1 = to_mpz1(a1);
        mpz const & v2 = to_mpz2(a2);
        if (v2 == 0)
            s.push(mk_vm_simple(0));
        else
            s.push(mk_vm_nat(v1 / v2));
    }
}

static void nat_mod(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    if (is_simple(a1) && is_simple(a2)) {
        unsigned v1 = cidx(a1);
        unsigned v2 = cidx(a2);
        if (v2 == 0)
            s.push(a1);
        else
            s.push(mk_vm_nat(v1 % v2));
    } else {
        mpz const & v1 = to_mpz1(a1);
        mpz const & v2 = to_mpz2(a2);
        if (v2 == 0)
            s.push(a1);
        else
            s.push(mk_vm_nat(v1 % v2));
    }
}

static void nat_gcd(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    mpz r;
    gcd(r, to_mpz1(a1), to_mpz2(a2));
    s.push(mk_vm_nat(r));
}

static void nat_has_decidable_eq(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    if (is_simple(a1) && is_simple(a2)) {
        return s.push(mk_vm_bool(cidx(a1) == cidx(a2)));
    } else {
        return s.push(mk_vm_bool(to_mpz1(a1) == to_mpz2(a2)));
    }
}

static void nat_decidable_le(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    if (is_simple(a1) && is_simple(a2)) {
        return s.push(mk_vm_bool(cidx(a1) <= cidx(a2)));
    } else {
        return s.push(mk_vm_bool(to_mpz1(a1) <= to_mpz2(a2)));
    }
}

static void nat_decidable_lt(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    if (is_simple(a1) && is_simple(a2)) {
        return s.push(mk_vm_bool(cidx(a1) < cidx(a2)));
    } else {
        return s.push(mk_vm_bool(to_mpz1(a1) < to_mpz2(a2)));
    }
}

void initialize_vm_nat() {
    declare_vm_builtin(get_nat_succ_name(),              1, nat_succ);
    declare_vm_builtin(get_nat_add_name(),               2, nat_add);
    declare_vm_builtin(get_nat_mul_name(),               2, nat_mul);
    declare_vm_builtin(get_nat_sub_name(),               2, nat_sub);
    declare_vm_builtin(get_nat_div_name(),               2, nat_div);
    declare_vm_builtin(get_nat_mod_name(),               2, nat_mod);
    declare_vm_builtin(get_nat_gcd_name(),               2, nat_gcd);
    declare_vm_builtin(get_nat_has_decidable_eq_name(),  2, nat_has_decidable_eq);
    declare_vm_builtin(get_nat_decidable_le_name(),      2, nat_decidable_le);
    declare_vm_builtin(get_nat_decidable_lt_name(),      2, nat_decidable_lt);
}

void finalize_vm_nat() {
}
}
