/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "library/constants.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"

namespace lean {
// =======================================
// Builtin nat operations

vm_obj mk_vm_nat(unsigned n) {
    if (n < LEAN_MAX_SMALL_NAT)
        return mk_vm_simple(n);
    else
        return mk_vm_mpz(mpz(n));
}

vm_obj mk_vm_nat(mpz const & n) {
    if (n < LEAN_MAX_SMALL_NAT)
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

static vm_obj nat_succ(vm_obj const & a) {
    if (is_simple(a)) {
        return mk_vm_nat(cidx(a) + 1);
    } else {
        return mk_vm_mpz(to_mpz1(a) + 1);
    }
}

static vm_obj nat_add(vm_obj const & a1, vm_obj const & a2) {
    if (is_simple(a1) && is_simple(a2)) {
        return mk_vm_nat(cidx(a1) + cidx(a2));
    } else {
        return mk_vm_mpz(to_mpz1(a1) + to_mpz2(a2));
    }
}

static vm_obj nat_mul(vm_obj const & a1, vm_obj const & a2) {
    if (is_simple(a1) && is_simple(a2)) {
        unsigned long long r = static_cast<unsigned long long>(cidx(a1)) * static_cast<unsigned long long>(cidx(a2));
        if (r < LEAN_MAX_SMALL_NAT) {
            return mk_vm_simple(r);
        }
    }
    return mk_vm_mpz(to_mpz1(a1) * to_mpz2(a2));
}

static vm_obj nat_sub(vm_obj const & a1, vm_obj const & a2) {
    if (is_simple(a1) && is_simple(a2)) {
        unsigned v1 = cidx(a1);
        unsigned v2 = cidx(a2);
        if (v2 > v1)
            return mk_vm_simple(0);
        else
            return mk_vm_nat(v1 - v2);
    } else {
        mpz const & v1 = to_mpz1(a1);
        mpz const & v2 = to_mpz2(a2);
        if (v2 > v1)
            return mk_vm_simple(0);
        else
            return mk_vm_nat(v1 - v2);
    }
}

static vm_obj nat_div(vm_obj const & a1, vm_obj const & a2) {
    if (is_simple(a1) && is_simple(a2)) {
        unsigned v1 = cidx(a1);
        unsigned v2 = cidx(a2);
        if (v2 == 0)
            return mk_vm_simple(0);
        else
            return mk_vm_nat(v1 / v2);
    } else {
        mpz const & v1 = to_mpz1(a1);
        mpz const & v2 = to_mpz2(a2);
        if (v2 == 0)
            return mk_vm_simple(0);
        else
            return mk_vm_nat(v1 / v2);
    }
}

static vm_obj nat_mod(vm_obj const & a1, vm_obj const & a2) {
    if (is_simple(a1) && is_simple(a2)) {
        unsigned v1 = cidx(a1);
        unsigned v2 = cidx(a2);
        if (v2 == 0)
            return a1;
        else
            return mk_vm_nat(v1 % v2);
    } else {
        mpz const & v1 = to_mpz1(a1);
        mpz const & v2 = to_mpz2(a2);
        if (v2 == 0)
            return a1;
        else
            return mk_vm_nat(v1 % v2);
    }
}

static vm_obj nat_gcd(vm_obj const & a1, vm_obj const & a2) {
    mpz r;
    gcd(r, to_mpz1(a1), to_mpz2(a2));
    return mk_vm_nat(r);
}

static vm_obj nat_has_decidable_eq(vm_obj const & a1, vm_obj const & a2) {
    if (is_simple(a1) && is_simple(a2)) {
        return mk_vm_bool(cidx(a1) == cidx(a2));
    } else {
        return mk_vm_bool(to_mpz1(a1) == to_mpz2(a2));
    }
}

static vm_obj nat_decidable_le(vm_obj const & a1, vm_obj const & a2) {
    if (is_simple(a1) && is_simple(a2)) {
        return mk_vm_bool(cidx(a1) <= cidx(a2));
    } else {
        return mk_vm_bool(to_mpz1(a1) <= to_mpz2(a2));
    }
}

static vm_obj nat_decidable_lt(vm_obj const & a1, vm_obj const & a2) {
    if (is_simple(a1) && is_simple(a2)) {
        return mk_vm_bool(cidx(a1) < cidx(a2));
    } else {
        return mk_vm_bool(to_mpz1(a1) < to_mpz2(a2));
    }
}

static void nat_rec(vm_state &) {
    /* recursors are implemented by the compiler */
    lean_unreachable();
}

static void nat_no_confusion(vm_state &) {
    /* no_confusion is implemented by the compiler */
    lean_unreachable();
}

static vm_obj nat_to_string(vm_obj const & a) {
    std::ostringstream out;
    if (is_simple(a)) {
        out << cidx(a);
    } else {
        out << to_mpz(a);
    }
    return to_obj(out.str());
}

void initialize_vm_nat() {
    declare_vm_builtin(get_nat_succ_name(),              nat_succ);
    declare_vm_builtin(get_nat_add_name(),               nat_add);
    declare_vm_builtin(get_nat_mul_name(),               nat_mul);
    declare_vm_builtin(get_nat_sub_name(),               nat_sub);
    declare_vm_builtin(get_nat_div_name(),               nat_div);
    declare_vm_builtin(get_nat_mod_name(),               nat_mod);
    declare_vm_builtin(get_nat_gcd_name(),               nat_gcd);
    declare_vm_builtin(get_nat_has_decidable_eq_name(),  nat_has_decidable_eq);
    declare_vm_builtin(get_nat_decidable_le_name(),      nat_decidable_le);
    declare_vm_builtin(get_nat_decidable_lt_name(),      nat_decidable_lt);
    declare_vm_builtin(get_nat_cases_on_name(),          4, nat_rec);
    declare_vm_builtin(get_nat_rec_on_name(),            4, nat_rec);
    declare_vm_builtin(get_nat_no_confusion_name(),      5, nat_no_confusion);
    declare_vm_builtin(get_nat_no_confusion_type_name(), 3, nat_no_confusion);
    declare_vm_builtin(get_nat_to_string_name(),         nat_to_string);
}

void finalize_vm_nat() {
}
}
