/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include "kernel/expr.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "library/locals.h"
#include "library/sorry.h"
#include "library/util.h"
#include "library/expr_lt.h"
#include "library/deep_copy.h"
#include "library/comp_val.h"
#include "library/annotation.h"
#include "library/quote.h"
#include "library/string.h"
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_options.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_level.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_pos_info.h"
#include "library/compiler/simp_inductive.h"
#include "library/compiler/nat_value.h"

namespace lean {
struct vm_expr : public vm_external {
    expr m_val;
    vm_expr(expr const & v):m_val(v) {}
    virtual ~vm_expr() {}
    virtual void dealloc() override { delete this; }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_expr(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new vm_expr(m_val); }
};

bool is_expr(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_expr*>(to_external(o));
}

expr const & to_expr(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_expr*>(to_external(o)));
    return static_cast<vm_expr*>(to_external(o))->m_val;
}

vm_obj to_obj(expr const & e) {
    return mk_vm_external(new vm_expr(e));
}

vm_obj to_obj(optional<expr> const & e) {
    return e ? mk_vm_some(to_obj(*e)) : mk_vm_none();
}

binder_info to_binder_info(vm_obj const & o) {
    lean_assert(is_simple(o));
    return static_cast<binder_info>(cidx(o));
}

vm_obj to_obj(binder_info bi) {
    return mk_vm_simple(static_cast<unsigned>(bi));
}

// The expr_bvar_intro function has an _intro suffix so that it doesn't clash
// with the expr_bvar class. This confuses GDB's python interface. The other
// introduction rules have the suffix for the same reason.

vm_obj expr_bvar_intro(vm_obj const & n) {
    return to_obj(mk_bvar(nat(vm_nat_to_mpz1(n))));
}

vm_obj expr_sort_intro(vm_obj const & l) {
    return to_obj(mk_sort(to_level(l)));
}

vm_obj expr_lit_intro(vm_obj const & l) {
    switch (cidx(l)) {
    case 0:
        return to_obj(mk_lit(literal(to_string(cfield(l, 0)).c_str())));
    case 1:
        return to_obj(mk_lit(literal(vm_nat_to_mpz1(cfield(l, 0)))));
    }
    lean_unreachable();
}

vm_obj expr_const_intro(vm_obj const & n, vm_obj const & ls) {
    return to_obj(mk_constant(to_name(n), to_levels(ls)));
}

vm_obj expr_mvar_intro(vm_obj const & n, vm_obj const & pp_n, vm_obj const & t) {
    return to_obj(mk_metavar(to_name(n), to_name(pp_n), to_expr(t)));
}

vm_obj expr_fvar_const_intro(vm_obj const & n) {
    return to_obj(mk_local(to_name(n), to_name(n), expr(), mk_binder_info()));
}

vm_obj expr_app_intro(vm_obj const & f, vm_obj const & a) {
    return to_obj(mk_app(to_expr(f), to_expr(a)));
}

vm_obj expr_lam_intro(vm_obj const & n, vm_obj const & bi, vm_obj const & t, vm_obj const & b) {
    return to_obj(mk_lambda(to_name(n), to_expr(t), to_expr(b), to_binder_info(bi)));
}

vm_obj expr_pi_intro(vm_obj const & n, vm_obj const & bi, vm_obj const & t, vm_obj const & b) {
    return to_obj(mk_pi(to_name(n), to_expr(t), to_expr(b), to_binder_info(bi)));
}

vm_obj expr_elet_intro(vm_obj const & n, vm_obj const & t, vm_obj const & v, vm_obj const & b) {
    return to_obj(mk_let(to_name(n), to_expr(t), to_expr(v), to_expr(b)));
}

/*
inductive data_value
| of_string (v : string)
| of_nat    (v : nat)
| of_bool   (v : bool)
| of_name   (v : name)
*/
vm_obj to_obj(data_value const & d) {
    switch (d.kind()) {
    case data_value_kind::String: return mk_vm_constructor(0, to_obj(d.get_string().to_std_string()));
    case data_value_kind::Nat:    return mk_vm_constructor(1, mk_vm_nat(d.get_nat().to_mpz()));
    case data_value_kind::Bool:   return mk_vm_constructor(2, mk_vm_bool(d.get_bool()));
    case data_value_kind::Name:   return mk_vm_constructor(3, to_obj(d.get_name()));
    }
    lean_unreachable();
}

vm_obj to_obj(kvmap const & m) {
    buffer<vm_obj> objs;
    for (pair_ref<name, data_value> const & p : m) {
        objs.push_back(mk_vm_pair(to_obj(p.fst()), to_obj(p.snd())));
    }
    return to_obj(objs);
}

unsigned expr_cases_on(vm_obj const & o, buffer<vm_obj> & data) {
    expr const & e = to_expr(o);
    switch (e.kind()) {
    case expr_kind::BVar:
        data.push_back(mk_vm_nat(bvar_idx(e).to_mpz()));
        break;
    case expr_kind::Sort:
        data.push_back(to_obj(sort_level(e)));
        break;
    case expr_kind::Const:
        data.push_back(to_obj(const_name(e)));
        data.push_back(to_obj(const_levels(e)));
        break;
    case expr_kind::MVar:
        data.push_back(to_obj(mlocal_name(e)));
        data.push_back(to_obj(mlocal_pp_name(e)));
        data.push_back(to_obj(mlocal_type(e)));
        break;
    case expr_kind::FVar:
        data.push_back(to_obj(mlocal_name(e)));
        break;
    case expr_kind::App:
        data.push_back(to_obj(app_fn(e)));
        data.push_back(to_obj(app_arg(e)));
        break;
    case expr_kind::Lambda:
    case expr_kind::Pi:
        data.push_back(to_obj(binding_name(e)));
        data.push_back(to_obj(binding_info(e)));
        data.push_back(to_obj(binding_domain(e)));
        data.push_back(to_obj(binding_body(e)));
        break;
    case expr_kind::Let:
        data.push_back(to_obj(let_name(e)));
        data.push_back(to_obj(let_type(e)));
        data.push_back(to_obj(let_value(e)));
        data.push_back(to_obj(let_body(e)));
        break;
    case expr_kind::Lit:
        switch (lit_value(e).kind()) {
        case literal_kind::String:
            data.push_back(mk_vm_constructor(0, to_obj(std::string(lit_value(e).get_string().to_std_string()))));
            break;
        case literal_kind::Nat:
            data.push_back(mk_vm_constructor(1, mk_vm_nat(lit_value(e).get_nat().to_mpz())));
            break;
        }
        break;
    case expr_kind::MData:
        data.push_back(to_obj(mdata_data(e)));
        data.push_back(to_obj(mdata_expr(e)));
        break;
    case expr_kind::Proj:
        data.push_back(to_obj(proj_idx(e)));
        data.push_back(to_obj(proj_expr(e)));
        break;
    case expr_kind::Quote:
        data.push_back(mk_vm_bool(quote_is_reflected(e)));
        data.push_back(to_obj(quote_value(e)));
        break;
    }
    return static_cast<unsigned>(e.kind());
}

vm_obj expr_has_decidable_eq(vm_obj const & o1, vm_obj const & o2) {
    return mk_vm_bool(is_bi_equal(to_expr(o1), to_expr(o2)));
}

vm_obj expr_alpha_eqv(vm_obj const & o1, vm_obj const & o2) {
    return mk_vm_bool(to_expr(o1) == to_expr(o2));
}

vm_obj expr_to_string(vm_obj const & l) {
    std::ostringstream out;
    out << to_expr(l);
    return to_obj(out.str());
}

vm_obj expr_lt(vm_obj const & o1, vm_obj const & o2) {
    return mk_vm_bool(is_lt(to_expr(o1), to_expr(o2), true));
}

vm_obj expr_lex_lt(vm_obj const & o1, vm_obj const & o2) {
    return mk_vm_bool(is_lt(to_expr(o1), to_expr(o2), false));
}

vm_obj expr_fold(vm_obj const &, vm_obj const & e, vm_obj const & a, vm_obj const & fn) {
    vm_obj r = a;
    for_each(to_expr(e), [&](expr const & o, unsigned d) {
            r = invoke(fn, to_obj(o), mk_vm_nat(d), r);
            return true;
        });
    return r;
}

vm_obj expr_has_bvar_idx(vm_obj const & e, vm_obj const & u) {
    if (auto n = try_to_unsigned(u)) {
        return mk_vm_bool(has_loose_bvar(to_expr(e), *n));
    } else {
        return mk_vm_false();
    }
}

vm_obj expr_hash(vm_obj const & e) {
    unsigned r = hash(to_expr(e)) % LEAN_VM_MAX_SMALL_NAT;
    return mk_vm_simple(r); // make sure it is a simple value
}

vm_obj expr_get_nat_value(vm_obj const & o) {
    expr e = to_expr(o);
    if (is_nat_value(e)) {
        auto n = mk_vm_nat(get_nat_value_value(e));
        return mk_vm_constructor(1, { n });
    } else {
        return mk_vm_simple(0);
    }
}

vm_obj expr_collect_univ_params(vm_obj const & o) {
    names param_list;
    collect_univ_params(to_expr(o), name_set()).for_each(
            [&] (name const & n) { param_list = cons(n, param_list); });
    return to_obj(param_list);
}

// TODO(Leo): move to a different file
vm_obj vm_mk_nat_val_ne_proof(vm_obj const & a, vm_obj const & b) {
    return to_obj(mk_nat_val_ne_proof(to_expr(a), to_expr(b)));
}

vm_obj vm_mk_nat_val_lt_proof(vm_obj const & a, vm_obj const & b) {
    return to_obj(mk_nat_val_lt_proof(to_expr(a), to_expr(b)));
}

vm_obj vm_mk_nat_val_le_proof(vm_obj const & a, vm_obj const & b) {
    return to_obj(mk_nat_val_le_proof(to_expr(a), to_expr(b)));
}

vm_obj vm_mk_fin_val_ne_proof(vm_obj const & a, vm_obj const & b) {
    return to_obj(mk_fin_val_ne_proof(to_expr(a), to_expr(b)));
}

vm_obj vm_mk_char_val_ne_proof(vm_obj const & a, vm_obj const & b) {
    return to_obj(mk_char_val_ne_proof(to_expr(a), to_expr(b)));
}

vm_obj vm_mk_string_val_ne_proof(vm_obj const & a, vm_obj const & b) {
    return to_obj(mk_string_val_ne_proof(to_expr(a), to_expr(b)));
}

vm_obj expr_subst(vm_obj const & _e1, vm_obj const & _e2) {
    expr const & e1 = to_expr(_e1);
    expr const & e2 = to_expr(_e2);
    if (is_lambda(e1)) {
        return to_obj(instantiate(binding_body(e1), e2));
    } else {
        return to_obj(e1);
    }
}

vm_obj expr_is_annotation(vm_obj const & _e) {
    expr const & e = to_expr(_e);
    if (is_annotation(e)) {
        return mk_vm_some(mk_vm_pair(to_obj(get_annotation_kind(e)), to_obj(get_annotation_arg(e))));
    } else {
        return mk_vm_none();
    }
}

vm_obj reflect_expr(vm_obj const & e) {
    return to_obj(mk_elaborated_expr_quote(to_expr(e)));
}

vm_obj reflect_string(vm_obj const & s) {
    return to_obj(from_string(to_string(s)));
}

void initialize_vm_expr() {
    DECLARE_VM_BUILTIN(name({"expr", "var"}),              expr_bvar_intro);
    DECLARE_VM_BUILTIN(name({"expr", "lit"}),              expr_lit_intro);
    DECLARE_VM_BUILTIN(name({"expr", "fvar"}),             expr_fvar_const_intro);
    DECLARE_VM_BUILTIN(name({"expr", "sort"}),             expr_sort_intro);
    DECLARE_VM_BUILTIN(name({"expr", "const"}),            expr_const_intro);
    DECLARE_VM_BUILTIN(name({"expr", "mvar"}),             expr_mvar_intro);
    DECLARE_VM_BUILTIN(name({"expr", "app"}),              expr_app_intro);
    DECLARE_VM_BUILTIN(name({"expr", "lam"}),              expr_lam_intro);
    DECLARE_VM_BUILTIN(name({"expr", "pi"}),               expr_pi_intro);
    DECLARE_VM_BUILTIN(name({"expr", "elet"}),             expr_elet_intro);
    DECLARE_VM_BUILTIN(name({"expr", "has_decidable_eq"}), expr_has_decidable_eq);
    DECLARE_VM_BUILTIN(name({"expr", "alpha_eqv"}),        expr_alpha_eqv);
    DECLARE_VM_BUILTIN(name({"expr", "to_string"}),        expr_to_string);
    DECLARE_VM_BUILTIN(name({"expr", "lt"}),               expr_lt);
    DECLARE_VM_BUILTIN(name({"expr", "lex_lt"}),           expr_lex_lt);
    DECLARE_VM_BUILTIN(name({"expr", "fold"}),             expr_fold);
    DECLARE_VM_BUILTIN(name({"expr", "subst"}),            expr_subst);
    DECLARE_VM_BUILTIN(name({"expr", "has_bvar_idx"}),     expr_has_bvar_idx);
    DECLARE_VM_BUILTIN(name({"expr", "hash"}),             expr_hash);

    DECLARE_VM_CASES_BUILTIN(name({"expr", "cases_on"}),   expr_cases_on);

    DECLARE_VM_BUILTIN(name("string", "reflect"),           reflect_string);
    DECLARE_VM_BUILTIN(name("expr", "reflect"),             reflect_expr);

    DECLARE_VM_BUILTIN(name("mk_nat_val_ne_proof"),        vm_mk_nat_val_ne_proof);
    DECLARE_VM_BUILTIN(name("mk_nat_val_lt_proof"),        vm_mk_nat_val_lt_proof);
    DECLARE_VM_BUILTIN(name("mk_nat_val_le_proof"),        vm_mk_nat_val_le_proof);
    DECLARE_VM_BUILTIN(name("mk_fin_val_ne_proof"),        vm_mk_fin_val_ne_proof);
    DECLARE_VM_BUILTIN(name("mk_char_val_ne_proof"),       vm_mk_char_val_ne_proof);
    DECLARE_VM_BUILTIN(name("mk_string_val_ne_proof"),     vm_mk_string_val_ne_proof);

    DECLARE_VM_BUILTIN(name("expr", "is_annotation"),      expr_is_annotation);
}

void finalize_vm_expr() {
}

void initialize_vm_expr_builtin_idxs() {
}
}
