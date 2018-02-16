/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"

namespace lean {
// =======================================
// Builtin nat operations

vm_obj mk_vm_nat(unsigned n) {
    if (LEAN_LIKELY(n < LEAN_MAX_SMALL_NAT))
        return mk_vm_simple(n);
    else
        return mk_vm_mpz(mpz(n));
}

vm_obj mk_vm_nat(mpz const & n) {
    if (LEAN_LIKELY(n < LEAN_MAX_SMALL_NAT))
        return mk_vm_simple(n.get_unsigned_int());
    else
        return mk_vm_mpz(n);
}

unsigned to_unsigned(vm_obj const & o) {
    if (LEAN_LIKELY(is_simple(o)))
        return cidx(o);
    else
        return to_mpz(o).get_unsigned_int();
}

optional<unsigned> try_to_unsigned(vm_obj const & o) {
    if (LEAN_LIKELY(is_simple(o))) {
        return optional<unsigned>(cidx(o));
    } else {
        mpz const & v = to_mpz(o);
        if (v.is_unsigned_int())
            return optional<unsigned>(v.get_unsigned_int());
        else
            return optional<unsigned>();
    }
}

unsigned force_to_unsigned(vm_obj const & o, unsigned def) {
    if (auto r = try_to_unsigned(o))
        return *r;
    else
        return def;
}

size_t force_to_size_t(vm_obj const & o, size_t def) {
    // TODO(Leo): fix size_t is 8 bytes in 64-bit machines
    if (auto r = try_to_unsigned(o))
        return *r;
    else
        return def;
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

mpz const & vm_nat_to_mpz1(vm_obj const & o) {
    return to_mpz1(o);
}

mpz const & vm_nat_to_mpz2(vm_obj const & o) {
    return to_mpz2(o);
}

vm_obj nat_succ(vm_obj const & a) {
    if (LEAN_LIKELY(is_simple(a))) {
        return mk_vm_nat(cidx(a) + 1);
    } else {
        return mk_vm_mpz(to_mpz1(a) + 1);
    }
}

vm_obj nat_add(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
        return mk_vm_nat(cidx(a1) + cidx(a2));
    } else {
        return mk_vm_mpz(to_mpz1(a1) + to_mpz2(a2));
    }
}

vm_obj nat_mul(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
        unsigned long long r = static_cast<unsigned long long>(cidx(a1)) * static_cast<unsigned long long>(cidx(a2));
        if (LEAN_LIKELY(r < LEAN_MAX_SMALL_NAT)) {
            return mk_vm_simple(r);
        }
    }
    return mk_vm_mpz(to_mpz1(a1) * to_mpz2(a2));
}

vm_obj nat_sub(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
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

vm_obj nat_div(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
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

vm_obj nat_mod(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
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

vm_obj nat_gcd(vm_obj const & a1, vm_obj const & a2) {
    mpz r;
    gcd(r, to_mpz1(a1), to_mpz2(a2));
    return mk_vm_nat(r);
}

vm_obj nat_shiftl(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
        unsigned v1 = cidx(a1);
        unsigned v2 = cidx(a2);
        if (v2 <= 31 && v1 >> (31 - v2) == 0) // LEAN_MAX_SMALL_NAT = 1 >> 31
            return mk_vm_nat(v1 << v2);
    }
    mpz v1 = to_mpz1(a1);
    mul2k(v1, v1, to_unsigned(a2));
    return mk_vm_mpz(v1);
}

vm_obj nat_shiftr(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
        int v2 = cidx(a2);
        return v2 < 32 ? mk_vm_nat(cidx(a1) >> v2) : mk_vm_simple(0);
    } else {
        mpz v1 = to_mpz1(a1);
        div2k(v1, v1, to_unsigned(a2));
        return mk_vm_mpz(v1);
    }
}

vm_obj nat_div2(vm_obj const & a) {
    if (LEAN_LIKELY(is_simple(a))) {
        return mk_vm_nat(cidx(a) >> 1);
    } else {
        mpz v = to_mpz1(a);
        div2k(v, v, 1);
        return mk_vm_mpz(v);
    }
}

vm_obj nat_bodd(vm_obj const & a1) {
    if (LEAN_LIKELY(is_simple(a1))) {
        return mk_vm_bool((cidx(a1) & 1u) != 0);
    } else {
        mpz const & v1 = to_mpz1(a1);
        return mk_vm_bool(v1.test_bit(0));
    }
}

vm_obj nat_bodd_div2(vm_obj const & a) {
    return mk_vm_pair(nat_bodd(a), nat_div2(a));
}

vm_obj nat_land(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
        return mk_vm_nat(cidx(a1) & cidx(a2));
    } else {
        return mk_vm_mpz(to_mpz1(a1) & to_mpz2(a2));
    }
}

vm_obj nat_lor(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
        return mk_vm_nat(cidx(a1) | cidx(a2));
    } else {
        return mk_vm_mpz(to_mpz1(a1) | to_mpz2(a2));
    }
}

vm_obj nat_lxor(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
        return mk_vm_nat(cidx(a1) ^ cidx(a2));
    } else {
        return mk_vm_mpz(to_mpz1(a1) ^ to_mpz2(a2));
    }
}

vm_obj nat_ldiff(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
        return mk_vm_nat(cidx(a1) & ~cidx(a2));
    } else {
        return mk_vm_mpz(to_mpz1(a1) & ~to_mpz2(a2));
    }
}

vm_obj nat_test_bit(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
        return mk_vm_bool((cidx(a1) & (1u << cidx(a2))) != 0);
    } else {
        mpz const & v1 = to_mpz1(a1);
        mpz const & v2 = to_mpz2(a2);
        if (v2.is_unsigned_long_int())
            return mk_vm_bool(v1.test_bit(v2.get_unsigned_long_int()));
        else
            return mk_vm_bool(false);
    }
}

vm_obj nat_decidable_eq(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
        return mk_vm_bool(cidx(a1) == cidx(a2));
    } else {
        return mk_vm_bool(to_mpz1(a1) == to_mpz2(a2));
    }
}

vm_obj nat_decidable_le(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
        return mk_vm_bool(cidx(a1) <= cidx(a2));
    } else {
        return mk_vm_bool(to_mpz1(a1) <= to_mpz2(a2));
    }
}

vm_obj nat_decidable_lt(vm_obj const & a1, vm_obj const & a2) {
    if (LEAN_LIKELY(is_simple(a1) && is_simple(a2))) {
        return mk_vm_bool(cidx(a1) < cidx(a2));
    } else {
        return mk_vm_bool(to_mpz1(a1) < to_mpz2(a2));
    }
}

void nat_rec(vm_state &) {
    /* recursors are implemented by the compiler */
    lean_unreachable();
}

void nat_no_confusion(vm_state &) {
    /* no_confusion is implemented by the compiler */
    lean_unreachable();
}

vm_obj nat_repr(vm_obj const & a) {
    std::ostringstream out;
    if (is_simple(a)) {
        out << cidx(a);
    } else {
        out << to_mpz(a);
    }
    return to_obj(out.str());
}

vm_obj nat_repeat(vm_obj const &, vm_obj const & f, vm_obj const & n, vm_obj const & a) {
    if (LEAN_LIKELY(is_simple(n))) {
        unsigned _n = cidx(n);
        vm_obj   r  = a;
        for (unsigned i = 0; i < _n ; i++) {
            r = invoke(f, mk_vm_simple(i), r);
        }
        return r;
    } else {
        mpz _n = to_mpz(n);
        mpz i(0);
        vm_obj r = a;
        while (i < _n) {
            r = invoke(f, mk_vm_nat(i), r);
            i++;
        }
        return r;
    }
}

void initialize_vm_nat() {
    DECLARE_VM_BUILTIN(name({"nat", "succ"}),             nat_succ);
    DECLARE_VM_BUILTIN(name({"nat", "add"}),              nat_add);
    DECLARE_VM_BUILTIN(name({"nat", "mul"}),              nat_mul);
    DECLARE_VM_BUILTIN(name({"nat", "sub"}),              nat_sub);
    DECLARE_VM_BUILTIN(name({"nat", "div"}),              nat_div);
    DECLARE_VM_BUILTIN(name({"nat", "mod"}),              nat_mod);
    DECLARE_VM_BUILTIN(name({"nat", "gcd"}),              nat_gcd);
    DECLARE_VM_BUILTIN(name({"nat", "decidable_eq"}),     nat_decidable_eq);
    DECLARE_VM_BUILTIN(name({"nat", "decidable_le"}),     nat_decidable_le);
    DECLARE_VM_BUILTIN(name({"nat", "decidable_lt"}),     nat_decidable_lt);
    DECLARE_VM_BUILTIN(name({"nat", "repr"}),             nat_repr);
    DECLARE_VM_BUILTIN(name({"nat", "repeat"}),           nat_repeat);
    DECLARE_VM_BUILTIN(name({"nat", "bodd"}),             nat_bodd);
    DECLARE_VM_BUILTIN(name({"nat", "div2"}),             nat_div2);
    DECLARE_VM_BUILTIN(name({"nat", "bodd_div2"}),        nat_bodd_div2);
    DECLARE_VM_BUILTIN(name({"nat", "shiftl"}),           nat_shiftl);
    DECLARE_VM_BUILTIN(name({"nat", "shiftr"}),           nat_shiftr);
    DECLARE_VM_BUILTIN(name({"nat", "lor"}),              nat_lor);
    DECLARE_VM_BUILTIN(name({"nat", "land"}),             nat_land);
    DECLARE_VM_BUILTIN(name({"nat", "ldiff"}),            nat_ldiff);
    DECLARE_VM_BUILTIN(name({"nat", "lxor"}),             nat_lxor);
    DECLARE_VM_BUILTIN(name({"nat", "test_bit"}),         nat_test_bit);

    declare_vm_builtin(name({"nat", "cases_on"}),          "nat_rec",          4, nat_rec);
    declare_vm_builtin(name({"nat", "rec_on"}),            "nat_rec",          4, nat_rec);
    declare_vm_builtin(name({"nat", "no_confusion"}),      "nat_no_confusion", 5, nat_no_confusion);
    declare_vm_builtin(name({"nat", "no_confusion_type"}), "nat_no_confusion", 3, nat_no_confusion);
}

void finalize_vm_nat() {
}
}
