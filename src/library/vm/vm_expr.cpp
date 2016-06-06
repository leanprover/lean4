/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include "kernel/expr.h"
#include "library/expr_lt.h"
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_options.h"
#include "library/vm/vm_level.h"

namespace lean {
struct vm_macro_definition : public vm_external {
    macro_definition m_val;
    vm_macro_definition(macro_definition const & v):m_val(v) {}
    virtual ~vm_macro_definition() {}
};

macro_definition const & to_macro_definition(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_macro_definition*>(to_external(o)));
    return static_cast<vm_macro_definition*>(to_external(o))->m_val;
}

vm_obj to_obj(macro_definition const & d) {
    return mk_vm_external(new vm_macro_definition(d));
}

struct vm_expr : public vm_external {
    expr m_val;
    vm_expr(expr const & v):m_val(v) {}
    virtual ~vm_expr() {}
};

expr const & to_expr(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_expr*>(to_external(o)));
    return static_cast<vm_expr*>(to_external(o))->m_val;
}

vm_obj to_obj(expr const & e) {
    return mk_vm_external(new vm_expr(e));
}

list<expr> to_list_expr(vm_obj const & o) {
    if (is_simple(o))
        return list<expr>();
    else
        return list<expr>(to_expr(cfield(o, 0)), to_list_expr(cfield(o, 1)));
}

void to_buffer_expr(vm_obj const & o, buffer<expr> & r) {
    if (is_simple(o)) {
        return;
    } else {
        r.push_back(to_expr(cfield(o, 0)));
        to_buffer_expr(cfield(o, 1), r);
    }
}

vm_obj to_obj(buffer<expr> const & ls) {
    vm_obj r = mk_vm_simple(0);
    unsigned i = ls.size();
    while (i > 0) {
        --i;
        r = mk_vm_constructor(1, to_obj(ls[i]), r);
    }
    return r;
}

vm_obj to_obj(list<expr> const & ls) {
    buffer<expr> ls_buff;
    to_buffer(ls, ls_buff);
    return to_obj(ls_buff);
}

binder_info to_binder_info(vm_obj const & o) {
    lean_assert(is_simple(o));
    /*
      inductive binder_info :=
      | default | implicit | strict_implicit | inst_implicit | other
    */
    switch (cidx(o)) {
    case 0:  return binder_info();
    case 1:  return mk_implicit_binder_info();
    case 2:  return mk_strict_implicit_binder_info();
    case 3:  return mk_inst_implicit_binder_info();
    default: return mk_rec_info(true);
    }
}

vm_obj to_obj(binder_info const & bi) {
    if (bi.is_implicit())
        return mk_vm_simple(1);
    else if (bi.is_strict_implicit())
        return mk_vm_simple(2);
    else if (bi.is_inst_implicit())
        return mk_vm_simple(3);
    else if (bi.is_rec())
        return mk_vm_simple(4);
    else
        return mk_vm_simple(0);
}

vm_obj expr_var(vm_obj const & n) {
    return to_obj(mk_var(to_unsigned(n)));
}

vm_obj expr_sort(vm_obj const & l) {
    return to_obj(mk_sort(to_level(l)));
}

vm_obj expr_const(vm_obj const & n, vm_obj const & ls) {
    return to_obj(mk_constant(to_name(n), to_list_level(ls)));
}

vm_obj expr_meta(vm_obj const & n, vm_obj const & t) {
    return to_obj(mk_metavar(to_name(n), to_expr(t)));
}

vm_obj expr_free_var(vm_obj const & n, vm_obj const & ppn, vm_obj const & bi, vm_obj const & t) {
    return to_obj(mk_local(to_name(n), to_name(ppn), to_expr(t), to_binder_info(bi)));
}

vm_obj expr_app(vm_obj const & f, vm_obj const & a) {
    return to_obj(mk_app(to_expr(f), to_expr(a)));
}

vm_obj expr_lam(vm_obj const & n, vm_obj const & bi, vm_obj const & t, vm_obj const & b) {
    return to_obj(mk_lambda(to_name(n), to_expr(t), to_expr(b), to_binder_info(bi)));
}

vm_obj expr_pi(vm_obj const & n, vm_obj const & bi, vm_obj const & t, vm_obj const & b) {
    return to_obj(mk_pi(to_name(n), to_expr(t), to_expr(b), to_binder_info(bi)));
}

vm_obj expr_elet(vm_obj const & n, vm_obj const & t, vm_obj const & v, vm_obj const & b) {
    return to_obj(mk_let(to_name(n), to_expr(t), to_expr(v), to_expr(b)));
}

vm_obj expr_macro(vm_obj const & d, vm_obj const & n, vm_obj const & fn) {
    unsigned sz = to_unsigned(n);
    buffer<expr> args;
    for (unsigned i = 0; i < sz; i++) {
        args.push_back(to_expr(invoke(fn, mk_vm_nat(i))));
    }
    return to_obj(mk_macro(to_macro_definition(d), args.size(), args.data()));
}

vm_obj expr_macro_arg(vm_obj const & m, vm_obj const & i) {
    return to_obj(macro_arg(to_expr(m), to_unsigned(i)));
}

static unsigned g_expr_macro_arg_fun_idx = -1;

unsigned expr_cases_on(vm_obj const & o, buffer<vm_obj> & data) {
    expr const & e = to_expr(o);
    switch (e.kind()) {
    case expr_kind::Var:
        data.push_back(mk_vm_nat(var_idx(e)));
        break;
    case expr_kind::Sort:
        data.push_back(to_obj(sort_level(e)));
        break;
    case expr_kind::Constant:
        data.push_back(to_obj(const_name(e)));
        data.push_back(to_obj(const_levels(e)));
        break;
    case expr_kind::Meta:
        data.push_back(to_obj(mlocal_name(e)));
        data.push_back(to_obj(mlocal_type(e)));
        break;
    case expr_kind::Local:
        data.push_back(to_obj(mlocal_name(e)));
        data.push_back(to_obj(local_pp_name(e)));
        data.push_back(to_obj(local_info(e)));
        data.push_back(to_obj(mlocal_type(e)));
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
    case expr_kind::Macro:
        data.push_back(to_obj(macro_def(e)));
        data.push_back(to_obj(macro_num_args(e)));
        data.push_back(mk_vm_closure(g_expr_macro_arg_fun_idx, 1, &o));
        break;
    }
    return static_cast<unsigned>(e.kind());
}

vm_obj expr_mk_macro(vm_obj const & d, vm_obj const & es) {
    buffer<expr> args;
    to_buffer_expr(es, args);
    return to_obj(mk_macro(to_macro_definition(d), args.size(), args.data()));
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

void initialize_vm_expr() {
    DECLARE_VM_BUILTIN(name({"expr", "var"}),              expr_var);
    DECLARE_VM_BUILTIN(name({"expr", "sort"}),             expr_sort);
    DECLARE_VM_BUILTIN(name({"expr", "const"}),            expr_const);
    DECLARE_VM_BUILTIN(name({"expr", "meta"}),             expr_meta);
    DECLARE_VM_BUILTIN(name({"expr", "free_var"}),         expr_free_var);
    DECLARE_VM_BUILTIN(name({"expr", "app"}),              expr_app);
    DECLARE_VM_BUILTIN(name({"expr", "lam"}),              expr_lam);
    DECLARE_VM_BUILTIN(name({"expr", "pi"}),               expr_pi);
    DECLARE_VM_BUILTIN(name({"expr", "elet"}),             expr_elet);
    DECLARE_VM_BUILTIN("_expr_macro_arg",                  expr_macro_arg);
    DECLARE_VM_BUILTIN(name({"expr", "macro"}),            expr_macro);
    DECLARE_VM_BUILTIN(name({"expr", "mk_macro"}),         expr_mk_macro);
    DECLARE_VM_BUILTIN(name({"expr", "has_decidable_eq"}), expr_has_decidable_eq);
    DECLARE_VM_BUILTIN(name({"expr", "alpha_eqv"}),        expr_alpha_eqv);
    DECLARE_VM_BUILTIN(name({"expr", "to_string"}),        expr_to_string);
    DECLARE_VM_BUILTIN(name({"expr", "lt"}),               expr_lt);
    DECLARE_VM_BUILTIN(name({"expr", "lex_lt"}),           expr_lex_lt);
    DECLARE_VM_CASES_BUILTIN(name({"expr", "cases_on"}),   expr_cases_on);
}

void finalize_vm_expr() {
}

void initialize_vm_expr_builtin_idxs() {
    g_expr_macro_arg_fun_idx = *get_vm_builtin_idx(name("_expr_macro_arg"));
}
}
