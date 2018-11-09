/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_set>
#include <algorithm>
#include <string>
#include <limits>
#include "kernel/type_checker.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "kernel/kernel_exception.h"
#include "library/util.h"
#include "library/attribute_manager.h"
#include "library/aux_recursors.h"
#include "library/replace_visitor.h"
#include "library/constants.h"
#include "library/compiler/util.h"

namespace lean {
optional<unsigned> is_enum_type(environment const & env, name const & I) {
    constant_info info  = env.get(I);
    if (!info.is_inductive()) return optional<unsigned>();
    unsigned n = 0;
    for (name const & c : info.to_inductive_val().get_cnstrs()) {
        if (is_pi(env.get(c).get_type()))
            return optional<unsigned>();
        if (n == std::numeric_limits<unsigned>::max())
            return optional<unsigned>();
        n++;
    }
    if (n < (1u << 8)) {
        return optional<unsigned>(1);
    } else if (n < (1u << 16)) {
        return optional<unsigned>(2);
    } else {
        return optional<unsigned>(4);
    }
}

static expr * g_uint8  = nullptr;
static expr * g_uint16 = nullptr;
static expr * g_uint32 = nullptr;
static expr * g_uint64 = nullptr;

optional<expr> to_uint_type(unsigned nbytes) {
    switch (nbytes) {
    case 1:  return some_expr(*g_uint8);
    case 2:  return some_expr(*g_uint16);
    case 4:  return some_expr(*g_uint32);
    case 8:  return some_expr(*g_uint64);
    default: return none_expr();
    }
}

unsigned get_num_nested_lambdas(expr e) {
    unsigned r = 0;
    while (is_lambda(e)) {
        r++;
        e = binding_body(e);
    }
    return r;
}

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

bool has_inline_if_reduce_attribute(environment const & env, name const & n) {
    if (has_attribute(env, "inline_if_reduce", n))
        return true;
    if (is_internal_name(n) && !n.is_atomic()) {
        /* Auxiliary declarations such as `f._main` are considered to be marked as `@[inline_if_reduce]`
           if `f` is marked. */
        return has_inline_if_reduce_attribute(env, n.get_prefix());
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

bool has_noinline_attribute(environment const & env, name const & n) {
    if (has_attribute(env, "noinline", n))
        return true;
    if (is_internal_name(n) && !n.is_atomic()) {
        /* Auxiliary declarations such as `f._main` are considered to be marked as `@[noinline]`
           if `f` is marked. */
        return has_noinline_attribute(env, n.get_prefix());
    }
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
        bool modified = false;
        for (expr & arg : args) {
            expr new_arg = visit(arg);
            if (!is_eqp(new_arg, arg))
                modified = true;
            arg = new_arg;
        }
        if (is_constant(fn)) {
            name const & n = const_name(fn);
            if (has_macro_inline_attribute(m_env, n)) {
                expr new_fn = instantiate_value_lparams(m_env.get(n), const_levels(fn));
                std::reverse(args.begin(), args.end());
                return visit(apply_beta(new_fn, args.size(), args.data()));
            }
        }
        expr new_fn = visit(fn);
        if (!modified && is_eqp(new_fn, fn))
            return e;
        else
            return mk_app(new_fn, args);
    }

    virtual expr visit_constant(expr const & e) override {
        name const & n = const_name(e);
        if (has_macro_inline_attribute(m_env, n)) {
            return visit(instantiate_value_lparams(m_env.get(n), const_levels(e)));
        } else {
            return e;
        }
    }
};

expr unfold_macro_defs(environment const & env, expr const & e) {
    return unfold_macro_defs_fn(env)(e);
}

bool is_cases_on_recursor(environment const & env, name const & n) {
    return ::lean::is_aux_recursor(env, n) && n.get_string() == "cases_on";
}

unsigned get_cases_on_arity(environment const & env, name const & c, bool before_erasure) {
    lean_assert(is_cases_on_recursor(env, c));
    inductive_val I_val = get_cases_on_inductive_val(env, c);
    unsigned nminors    = I_val.get_ncnstrs();
    if (before_erasure) {
        unsigned nparams    = I_val.get_nparams();
        unsigned nindices   = I_val.get_nindices();
        return nparams + 1 /* motive */ + nindices + 1 /* major */ + nminors;
    } else {
        return 1 /* major */ + nminors;
    }
}

unsigned get_cases_on_major_idx(environment const & env, name const & c, bool before_erasure) {
    if (before_erasure) {
        inductive_val I_val = get_cases_on_inductive_val(env, c);
        return I_val.get_nparams() + 1 /* motive */ + I_val.get_nindices();
    } else {
        return 0;
    }
}

expr get_cases_on_app_major(environment const & env, expr const & c, bool before_erasure) {
    lean_assert(is_cases_on_app(env, c));
    buffer<expr> args;
    expr const & fn = get_app_args(c, args);
    return args[get_cases_on_major_idx(env, const_name(fn), before_erasure)];
}

pair<unsigned, unsigned> get_cases_on_minors_range(environment const & env, name const & c, bool before_erasure) {
    inductive_val I_val = get_cases_on_inductive_val(env, c);
    unsigned nminors    = I_val.get_ncnstrs();
    if (before_erasure) {
        unsigned nparams    = I_val.get_nparams();
        unsigned nindices   = I_val.get_nindices();
        unsigned first_minor_idx = nparams + 1 /*motive*/ + nindices + 1 /* major */;
        return mk_pair(first_minor_idx, first_minor_idx + nminors);
    } else {
        return mk_pair(1, 1+nminors);
    }
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

expr replace_fvar(expr const & e, expr const & fvar, expr const & new_term) {
    if (!has_fvar(e)) return e;
    return replace(e, [&](expr const & e, unsigned) {
            if (!has_fvar(e)) return some_expr(e);
            if (is_fvar(e) && fvar_name(fvar) == fvar_name(e))
                return some_expr(new_term);
            return none_expr();
        });
}

void sort_fvars(local_ctx const & lctx, buffer<expr> & fvars) {
    std::sort(fvars.begin(), fvars.end(),
              [&](expr const & x, expr const & y) {
                  return lctx.get_local_decl(x).get_idx() < lctx.get_local_decl(y).get_idx();
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

static expr * g_neutral_expr     = nullptr;
static expr * g_unreachable_expr = nullptr;
static expr * g_object_type      = nullptr;

expr mk_enf_unreachable() {
    return *g_unreachable_expr;
}

expr mk_enf_neutral() {
    return *g_neutral_expr;
}

expr mk_enf_object_type() {
    return *g_object_type;
}

expr mk_enf_neutral_type() {
    return *g_neutral_expr;
}

bool is_enf_neutral(expr const & e) {
    return e == *g_neutral_expr;
}

bool is_enf_unreachable(expr const & e) {
    return e == *g_unreachable_expr;
}

bool is_enf_object_type(expr const & e) {
    return e == *g_object_type;
}

bool is_runtime_builtin_type(name const & n) {
    /* TODO(Leo): use an attribute? */
    return
        n == get_string_name() ||
        n == get_string_iterator_name() ||
        n == get_uint8_name()  ||
        n == get_uint16_name() ||
        n == get_uint32_name() ||
        n == get_uint64_name() ||
        n == get_usize_name()  ||
        // n == get_thunk_name()  ||  TODO(Leo): enable
        // n == get_task_name()   ||  TODO(Leo): enable
        // n == get_array_name()  ||  TODO(Leo): enable
        n == get_nat_name()    ||
        n == get_int_name();
}

bool is_runtime_scalar_type(name const & n) {
    return
        n == get_uint8_name()  ||
        n == get_uint16_name() ||
        n == get_uint32_name() ||
        n == get_uint64_name() ||
        n == get_usize_name();
}

bool is_runtime_builtin_cnstr(name const & n) {
    // TODO(Leo): add array type constructors, thunk constructor,
    // universe level constructors, and expression constructors.

    /* Remark: we don't need to include `nat.zero` and `nat.zero` because
       they are converted into literals or addition. */
    return
        n == get_string_mk_name() ||
        n == get_string_iterator_mk_name() ||
        n == get_int_of_nat_name() ||
        n == get_int_neg_succ_of_nat_name();
}

bool is_irrelevant_type(type_checker::state & st, local_ctx lctx, expr const & type) {
    if (is_sort(type) || type_checker(st, lctx).is_prop(type))
        return true;
    expr type_it = type;
    if (is_pi(type_it)) {
        while (is_pi(type_it)) {
            expr fvar = lctx.mk_local_decl(st.ngen(), binding_name(type_it), binding_domain(type_it));
            type_it = type_checker(st, lctx).whnf(instantiate(binding_body(type_it), fvar));
        }
        if (is_sort(type_it))
            return true;
    }
    return false;
}

void collect_used(expr const & e, std::unordered_set<name, name_hash> & S) {
    if (!has_fvar(e)) return;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_fvar(e)) return false;
            if (is_fvar(e)) { S.insert(fvar_name(e)); return false; }
            return true;
        });
}

expr mk_runtime_type(type_checker::state & st, local_ctx const & lctx, expr e) {
    try {
        type_checker tc(st, lctx);
        e = tc.whnf(e);
        if (is_constant(e)) {
            name const & c = const_name(e);
            if (is_runtime_scalar_type(c)) {
                return e;
            } else if (c == get_char_name()) {
                return mk_constant(get_uint32_name());
            } else if (optional<unsigned> nbytes = is_enum_type(st.env(), c)) {
                return *to_uint_type(*nbytes);
            } else {
                return mk_enf_object_type();
            }
        } else if (is_sort(e) || tc.is_prop(e)) {
            return mk_enf_neutral_type();
        } else {
            return mk_enf_object_type();
        }
    } catch (kernel_exception &) {
        return mk_enf_object_type();
    }
}

void initialize_compiler_util() {
    g_neutral_expr     = new expr(mk_constant("_neutral_"));
    g_unreachable_expr = new expr(mk_constant("_unreachable_"));
    g_object_type      = new expr(mk_constant("_obj_"));
    g_uint8            = new expr(mk_constant(get_uint8_name()));
    g_uint16           = new expr(mk_constant(get_uint16_name()));
    g_uint32           = new expr(mk_constant(get_uint32_name()));
    g_uint64           = new expr(mk_constant(get_uint64_name()));

    register_system_attribute(basic_attribute::with_check(
            "inline", "mark definition to always be inlined",
            [](environment const & env, name const & d, bool) -> void {
                auto decl = env.get(d);
                if (!decl.is_definition())
                    throw exception("invalid 'inline' use, only definitions can be marked as [inline]");
            }));

    register_system_attribute(basic_attribute::with_check(
            "inline_if_reduce", "mark definition to be inlined when resultant term after reduction is not a `cases_on` application.",
            [](environment const & env, name const & d, bool) -> void {
                auto decl = env.get(d);
                if (!decl.is_definition())
                    throw exception("invalid 'inline_if_reduce' use, only definitions can be marked as [inline_if_reduce]");
            }));

    register_system_attribute(basic_attribute::with_check(
            "noinline", "mark definition to never be inlined",
            [](environment const & env, name const & d, bool) -> void {
                auto decl = env.get(d);
                if (!decl.is_definition())
                    throw exception("invalid 'noinline' use, only definitions can be marked as [noinline]");
            }));

    register_system_attribute(basic_attribute::with_check(
            "macro_inline", "mark definition to always be inlined before ANF conversion",
            [](environment const & env, name const & d, bool) -> void {
                auto decl = env.get(d);
                if (!decl.is_definition())
                    throw exception("invalid 'macro_inline' use, only definitions can be marked as [macro_inline]");
            }));
}

void finalize_compiler_util() {
    delete g_neutral_expr;
    delete g_unreachable_expr;
    delete g_object_type;
    delete g_uint8;
    delete g_uint16;
    delete g_uint32;
    delete g_uint64;
}
}
