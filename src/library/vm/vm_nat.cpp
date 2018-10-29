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
    if (LEAN_LIKELY(n < LEAN_VM_MAX_SMALL_NAT))
        return mk_vm_simple(n);
    else
        return mk_vm_mpz(mpz(n));
}

vm_obj mk_vm_nat(mpz const & n) {
    if (LEAN_LIKELY(n < LEAN_VM_MAX_SMALL_NAT))
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
        if (LEAN_LIKELY(r < LEAN_VM_MAX_SMALL_NAT)) {
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

vm_obj nat_repr(vm_obj const & a) {
    std::ostringstream out;
    if (is_simple(a)) {
        out << cidx(a);
    } else {
        out << to_mpz(a);
    }
    return to_obj(out.str());
}

vm_obj mix_hash(vm_obj const & u1, vm_obj const & u2) {
    return mk_vm_nat(hash(to_unsigned(u1), to_unsigned(u2)));
}

void initialize_vm_nat() {
    DECLARE_VM_BUILTIN(name({"nat", "add"}),              nat_add);
    DECLARE_VM_BUILTIN(name({"nat", "mul"}),              nat_mul);
    DECLARE_VM_BUILTIN(name({"nat", "sub"}),              nat_sub);
    DECLARE_VM_BUILTIN(name({"nat", "div"}),              nat_div);
    DECLARE_VM_BUILTIN(name({"nat", "mod"}),              nat_mod);
    DECLARE_VM_BUILTIN(name({"nat", "gcd"}),              nat_gcd);
    DECLARE_VM_BUILTIN(name({"nat", "dec_eq"}),           nat_decidable_eq);
    DECLARE_VM_BUILTIN(name({"nat", "decidable_le"}),     nat_decidable_le);
    DECLARE_VM_BUILTIN(name({"nat", "decidable_lt"}),     nat_decidable_lt);
    DECLARE_VM_BUILTIN(name({"nat", "repr"}),             nat_repr);

    DECLARE_VM_BUILTIN(name("mix_hash"), mix_hash);
}

void finalize_vm_nat() {
}
}
