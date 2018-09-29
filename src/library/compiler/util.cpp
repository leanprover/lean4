/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/type_checker.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/attribute_manager.h"
#include "library/aux_recursors.h"
#include "library/replace_visitor.h"
#include "library/constants.h"
#include "library/compiler/util.h"

namespace lean {
bool has_inline_attribute(environment const & env, name const & n) {
    if (has_attribute(env, "inline", n))
        return true;
    if (is_internal_name(n) && !n.is_atomic()) {
        /* Auxiliary declarations such as `f._main` are considered to be marked as `@[inline]`
           if `f` is marked. */
        return has_inline_attribute(env, n.get_prefix());
    }
    return false;
}

bool has_macro_inline_attribute(environment const & env, name const & n) {
    if (has_attribute(env, "macro_inline", n))
        return true;
    if (is_internal_name(n) && !n.is_atomic()) {
        /* Auxiliary declarations such as `f._main` are considered to be marked as `@[macro_inline]`
           if `f` is marked. */
        return has_macro_inline_attribute(env, n.get_prefix());
    }
    return false;
}

bool has_noinline_attribute(environment const & /* env */, name const & /* n */) {
    return false;
}

bool is_lcnf_atom(expr const & e) {
    switch (e.kind()) {
    case expr_kind::FVar: case expr_kind::Const: case expr_kind::Lit:
        return true;
    default:
        return false;
    }
}

class elim_trivial_let_decls_fn : public replace_visitor {
    virtual expr visit_let(expr const & e) override {
        if (is_lcnf_atom(let_value(e))) {
            return visit(instantiate(let_body(e), let_value(e)));
        } else {
            return replace_visitor::visit_let(e);
        }
    }
};

expr elim_trivial_let_decls(expr const & e) {
    return elim_trivial_let_decls_fn()(e);
}

struct unfold_macro_defs_fn : public replace_visitor {
    environment const & m_env;
    unfold_macro_defs_fn(environment const & env):m_env(env) {}

    virtual expr visit_app(expr const & e) override {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        expr new_fn   = visit(fn);
        bool modified = !is_eqp(fn, new_fn);
        for (expr & arg : args) {
            expr new_arg = visit(arg);
            if (!is_eqp(new_arg, arg))
                modified = true;
            arg = new_arg;
        }
        if (is_constant(new_fn)) {
            name const & n = const_name(new_fn);
            if (has_macro_inline_attribute(m_env, n)) {
                new_fn = instantiate_value_lparams(m_env.get(n), const_levels(new_fn));
                std::reverse(args.begin(), args.end());
                return visit(apply_beta(new_fn, args.size(), args.data()));
            }
        }
        if (!modified)
            return e;
        else
            return mk_app(new_fn, args);
    }
};

expr unfold_macro_defs(environment const & env, expr const & e) {
    return unfold_macro_defs_fn(env)(e);
}

expr cheap_beta_reduce(expr const & e) {
    if (!is_app(e)) return e;
    expr fn = get_app_fn(e);
    if (!is_lambda(fn)) return e;
    buffer<expr> args;
    get_app_args(e, args);
    unsigned i = 0;
    while (is_lambda(fn) && i < args.size()) {
        i++;
        fn = binding_body(fn);
    }
    if (!has_loose_bvars(fn)) {
        return mk_app(fn, args.size() - i, args.data() + i);
    } else if (is_bvar(fn)) {
        lean_assert(bvar_idx(fn) < i);
        return mk_app(args[i - bvar_idx(fn).get_small_value() - 1], args.size() - i, args.data() + i);
    } else {
        return e;
    }
}

bool is_cases_on_recursor(environment const & env, name const & n) {
    return ::lean::is_aux_recursor(env, n) && n.get_string() == "cases_on";
}

unsigned get_cases_on_arity(environment const & env, name const & c) {
    lean_assert(is_cases_on_recursor(env, c));
    inductive_val I_val = get_cases_on_inductive_val(env, c);
    unsigned nparams    = I_val.get_nparams();
    unsigned nindices   = I_val.get_nindices();
    unsigned nminors    = I_val.get_ncnstrs();
    return nparams + 1 /* motive */ + nindices + 1 /* major */ + nminors;
}

expr get_cases_on_app_major(environment const & env, expr const & c) {
    lean_assert(is_cases_on_app(env, c));
    buffer<expr> args;
    expr const & fn = get_app_args(c, args);
    inductive_val I_val = get_cases_on_inductive_val(env, fn);
    return args[I_val.get_nparams() + 1 /* motive */ + I_val.get_nindices()];
}

pair<unsigned, unsigned> get_cases_on_minors_range(environment const & env, name const & c) {
    inductive_val I_val = get_cases_on_inductive_val(env, c);
    unsigned nparams    = I_val.get_nparams();
    unsigned nindices   = I_val.get_nindices();
    unsigned nminors    = I_val.get_ncnstrs();
    unsigned first_minor_idx = nparams + 1 /*motive*/ + nindices + 1 /* major */;
    return mk_pair(first_minor_idx, first_minor_idx + nminors);
}

expr mk_lc_unreachable(type_checker::state & s, local_ctx const & lctx, expr const & type) {
    type_checker tc(s, lctx);
    level lvl = sort_level(tc.ensure_type(type));
    return mk_app(mk_constant(get_lc_unreachable_name(), {lvl}), type);
}

bool is_join_point_name(name const & n) {
    return !n.is_atomic() && n.is_string() && strncmp(n.get_string().data(), "_join", 5) == 0;
}

bool has_fvar(expr const & e, expr const & fvar) {
    if (!has_fvar(e)) return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_fvar(e)) return false;
            if (found) return false;
            if (is_fvar(e) && fvar_name(fvar) == fvar_name(e))
                found = true;
            return true;
        });
    return found;
}

void mark_used_fvars(expr const & e, buffer<expr> const & fvars, buffer<bool> & used) {
    used.resize(fvars.size(), false);
    if (!has_fvar(e) || fvars.empty())
        return;
    bool all_used = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_fvar(e)) return false;
            if (all_used) return false;
            if (is_fvar(e)) {
                all_used = true;
                for (unsigned i = 0; i < fvars.size(); i++) {
                    if (!used[i]) {
                        all_used = false;
                        if (fvar_name(fvars[i]) == fvar_name(e)) {
                            used[i] = true;
                            break;
                        }
                    }
                }
            }
            return true;
        });
}

expr replace_fvar(expr const & e, expr const & fvar, expr const & new_fvar) {
    if (!has_fvar(e)) return e;
    return replace(e, [&](expr const & e, unsigned) {
            if (!has_fvar(e)) return some_expr(e);
            if (is_fvar(e) && fvar_name(fvar) == fvar_name(e))
                return some_expr(new_fvar);
            return none_expr();
        });
}

unsigned get_lcnf_size(environment const & env, expr e) {
    unsigned r = 0;
    switch (e.kind()) {
    case expr_kind::BVar:  case expr_kind::MVar:
    case expr_kind::Sort:
    case expr_kind::Lit:   case expr_kind::FVar:
    case expr_kind::Pi:    case expr_kind::Proj:
    case expr_kind::MData:
        return 1;
    case expr_kind::Const:
        return 1;
    case expr_kind::Lambda:
        r = 1;
        while (is_lambda(e)) {
            e = binding_body(e);
        }
        return get_lcnf_size(env, e);
    case expr_kind::App:
        if (is_cases_on_app(env, e)) {
            expr const & c_fn   = get_app_fn(e);
            inductive_val I_val = env.get(const_name(c_fn).get_prefix()).to_inductive_val();
            unsigned nminors    = I_val.get_ncnstrs();
            r = 1;
            for (unsigned i = 0; i < nminors; i++) {
                lean_assert(is_app(e));
                r += get_lcnf_size(env, app_arg(e));
                e = app_fn(e);
            }
            return r;
        } else {
            return 1;
        }
    case expr_kind::Let:
        while (is_let(e)) {
            r += get_lcnf_size(env, let_value(e));
            e = let_body(e);
        }
        return r + get_lcnf_size(env, e);
    }
    lean_unreachable();
}
}
