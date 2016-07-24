/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/app_builder.h"
#include "library/constants.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/choice.h"
#include "library/typed_expr.h"
#include "library/compiler/rec_fn_macro.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/elaborator_exception.h"
#include "frontends/lean/elaborator.h"

namespace lean {
MK_THREAD_LOCAL_GET_DEF(type_context_cache_helper, get_tch);

static type_context_cache & get_type_context_cache_for(environment const & env, options const & o) {
    return get_tch().get_cache_for(env, o);
}

elaborator::elaborator(environment const & env, options const & opts, local_level_decls const & lls,
                       metavar_context const & mctx, local_context const & lctx):
    m_env(env), m_opts(opts), m_local_level_decls(lls),
    m_ctx(mctx, lctx, get_type_context_cache_for(env, opts), transparency_mode::Semireducible) {
}

format elaborator::pp(expr const & e) {
    formatter_factory const & factory = get_global_ios().get_formatter_factory();
    formatter fmt = factory(m_env, m_opts, m_ctx);
    return fmt(e);
}

format elaborator::pp_indent(expr const & e) {
    unsigned i = get_pp_indent(m_opts);
    return nest(i, line() + pp(e));
}

level elaborator::mk_univ_metavar() {
    level r = m_ctx.mk_univ_metavar_decl();
    m_uvar_stack.push_back(r);
    return r;
}

expr elaborator::mk_metavar(expr const & A) {
    expr r = copy_tag(A, m_ctx.mk_metavar_decl(m_ctx.lctx(), A));
    m_mvar_stack.push_back(r);
    return r;
}

expr elaborator::mk_type_metavar() {
    level l = mk_univ_metavar();
    return mk_metavar(mk_sort(l));
}

expr elaborator::mk_instance(expr const & C) {
    if (has_expr_metavar(C)) {
        expr inst = mk_metavar(C);
        m_instance_stack.push_back(inst);
        return inst;
    } else if (optional<expr> inst = m_ctx.mk_class_instance(C)) {
        return *inst;
    } else {
        throw_elaborator_exception(C, format("failed to synthesize type class instance for") + pp_indent(C));
    }
}

level elaborator::get_level(expr const & A) {
    return ::lean::get_level(m_ctx, A);
}

level elaborator::replace_univ_placeholder(level const & l) {
    auto fn = [&](level const & l) {
        if (is_placeholder(l))
            return some_level(mk_univ_metavar());
        else
            return none_level();
    };
    return replace(l, fn);
}

static bool contains_placeholder(level const & l) {
    bool contains = false;
    auto fn = [&](level const & l) {
        if (contains) return false;
        if (is_placeholder(l))
            contains = true;
        return true;
    };
    for_each(l, fn);
    return contains;
}

void elaborator::resolve_instances_from(unsigned old_sz) {
    unsigned j = old_sz;
    for (unsigned i = old_sz; i < m_instance_stack.size(); i++) {
        expr inst_mvar = m_instance_stack[i];
        if (is_mvar_assigned(inst_mvar))
            continue;
        expr C = instantiate_mvars(infer_type(inst_mvar));
        if (!has_expr_metavar(C)) {
            if (!assign_mvar(inst_mvar, mk_instance(C)))
                throw_elaborator_exception(inst_mvar, format("failed to assign type class instance to placeholder"));
        } else {
            m_instance_stack[j] = m_instance_stack[i];
            j++;
        }
    }
    m_instance_stack.shrink(j);
}

expr elaborator::ensure_function(expr const & e, expr const & ref) {
    // TODO(Leo): infer type and try to apply coercion to function if needed
    // ref is only needed for generating error messages
    return e;
}

expr elaborator::ensure_type(expr const & e, expr const & ref) {
    // TODO(Leo): infer e type, and apply coercions if needed.
    // ref is only needed for generating error messages
    return e;
}

expr elaborator::ensure_has_type(expr const & e, expr const & type, expr const & ref) {
    // TODO(Leo): infer e type, and apply coercions to type if needed.
    // ref is only needed for generating error messages
    return e;
}

expr elaborator::visit_typed_expr(expr const & e) {
    expr val      = get_typed_expr_expr(e);
    expr type     = get_typed_expr_type(e);
    expr new_type = ensure_type(visit(type, none_expr()), type);
    expr new_val  = visit(val, some_expr(new_type));
    return ensure_has_type(new_val, new_type, e);
}

expr elaborator::visit_prenum_core(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_prenum(e));
    mpz const & v  = prenum_value(e);
    tag e_tag      = e.get_tag();
    expr A;
    if (expected_type)
        A = *expected_type;
    else
        A = mk_type_metavar();
    level A_lvl = get_level(A);
    levels ls(A_lvl);
    if (v.is_neg())
        throw_elaborator_exception("invalid pre-numeral, it must be a non-negative value", e);
    if (v.is_zero()) {
        expr has_zero_A = mk_app(mk_constant(get_has_zero_name(), ls), A, e_tag);
        expr S          = mk_instance(has_zero_A);
        return mk_app(mk_app(mk_constant(get_zero_name(), ls), A, e_tag), S, e_tag);
    } else {
        expr has_one_A = mk_app(mk_constant(get_has_one_name(), ls), A, e_tag);
        expr S_one     = mk_instance(has_one_A);
        expr one       = mk_app(mk_app(mk_constant(get_one_name(), ls), A, e_tag), S_one, e_tag);
        if (v == 1) {
            return one;
        } else {
            expr has_add_A = mk_app(mk_constant(get_has_add_name(), ls), A, e_tag);
            expr S_add     = mk_instance(has_add_A);
            std::function<expr(mpz const & v)> convert = [&](mpz const & v) {
                lean_assert(v > 0);
                if (v == 1)
                    return one;
                else if (v % mpz(2) == 0) {
                    expr r = convert(v / 2);
                    return mk_app(mk_app(mk_app(mk_constant(get_bit0_name(), ls), A, e_tag), S_add, e_tag), r, e_tag);
                } else {
                    expr r = convert(v / 2);
                    return mk_app(mk_app(mk_app(mk_app(mk_constant(get_bit1_name(), ls), A, e_tag), S_one, e_tag), S_add, e_tag), r, e_tag);
                }
            };
            return convert(v);
        }
    }
}

expr elaborator::get_default_numeral_type() {
    // TODO(Leo): allow user to modify default?
    return mk_constant(get_nat_name());
}

expr elaborator::visit_prenum(expr const & e, optional<expr> const & expected_type) {
    unsigned old_sz = m_instance_stack.size();
    expr r = visit_prenum_core(e, expected_type);
    if (!expected_type) {
        expr t = infer_type(r);
        if (!assign_mvar(t, get_default_numeral_type()))
            throw_elaborator_exception("invalid numeral, failed to force numeral to be a nat", e);
        resolve_instances_from(old_sz);
    }
    if (m_instance_stack.size() != old_sz)
        throw_elaborator_exception("invalid numeral, failed to synthesize type class instances", e);
    return instantiate_mvars(r);
}

expr elaborator::visit_sort(expr const & e) {
    expr r = update_sort(e, replace_univ_placeholder(sort_level(e)));
    if (contains_placeholder(sort_level(e)))
        m_to_check_sorts.emplace_back(e, r);
    return r;
}

expr elaborator::visit_const_core(expr const & e) {
    declaration d = m_env.get(const_name(e));
    buffer<level> ls;
    for (level const & l : const_levels(e))
        ls.push_back(replace_univ_placeholder(l));
    unsigned num_univ_params = d.get_num_univ_params();
    if (num_univ_params < ls.size()) {
        throw_elaborator_exception(sstream() << "incorrect number of universe levels parameters for '"
                                   << const_name(e) << "', #" << num_univ_params
                                   << " expected, #" << ls.size() << " provided", e);
    }
    // "fill" with meta universe parameters
    for (unsigned i = ls.size(); i < num_univ_params; i++)
        ls.push_back(mk_univ_metavar());
    lean_assert(num_univ_params == ls.size());
    return update_constant(e, to_list(ls.begin(), ls.end()));
}

expr elaborator::visit_function(expr const & fn, bool has_args, expr const & ref) {
    expr r;
    switch (fn.kind()) {
    case expr_kind::Var:
    case expr_kind::App:
        lean_unreachable();  // LCOV_EXCL_LINE
    case expr_kind::Pi:
    case expr_kind::Meta:
    case expr_kind::Sort:
        throw_elaborator_exception("invalid application, function expected", ref);
    case expr_kind::Local:     r = fn; break;
    case expr_kind::Constant:  r = visit_const_core(fn); break;
    case expr_kind::Macro:     r = visit_macro(fn, none_expr()); break;
    case expr_kind::Lambda:    r = visit_lambda(fn, none_expr()); break;
    case expr_kind::Let:       r = visit_let(fn, none_expr()); break;
    }
    if (has_args)
        r = ensure_function(r, ref);
    return r;
}

void elaborator::filter_using_arity(buffer<expr> & fn, arg_mask amask, unsigned num_args) {
    if (fn.size() == 1) return; // do nothing
    // TODO(Leo): if there are more than one possibility, then discard alternatives number of explicit arguments.
}

expr elaborator::visit_app_core(expr fn, buffer<expr> const & args, optional<expr> const & expected_type) {
    arg_mask amask = arg_mask::Default;
    if (is_explicit(fn)) {
        fn   = get_explicit_arg(fn);
        amask = arg_mask::All;
    } else if (is_partial_explicit(fn)) {
        fn   = get_partial_explicit_arg(fn);
        amask = arg_mask::Simple;
    }
    buffer<expr> fns;
    if (is_choice(fn)) {
        if (amask != arg_mask::Default)
            throw_elaborator_exception("invalid explicit annotation, symbol is overloaded (solution: use fully qualified names)", fn);
        for (unsigned i = 0; i < get_num_choices(fn); i++) {
            fns.push_back(get_choice(fn, i));
        }
    } else {
        fns.push_back(fn);
    }
    bool has_args = !args.empty();
    for (expr & new_fn : fns) {
        new_fn = visit_function(new_fn, has_args, fn);
    }
    filter_using_arity(fns, amask, args.size());

    if (fns.size() == 1 && args.size() == 0)
        return fns[0]; // Easy case

    // TODO(Leo)
    lean_unreachable();
}

expr elaborator::visit_local(expr const & e, optional<expr> const & expected_type) {
    return visit_app_core(e, buffer<expr>(), expected_type);
}

expr elaborator::visit_constant(expr const & e, optional<expr> const & expected_type) {
    return visit_app_core(e, buffer<expr>(), expected_type);
}

expr elaborator::visit_app(expr const & e, optional<expr> const & expected_type) {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    return visit_app_core(fn, args, expected_type);
}

expr elaborator::visit_macro(expr const & e, optional<expr> const & expected_type) {
    if (is_as_is(e)) {
        return get_as_is_arg(e);
    } else if (is_prenum(e)) {
        return visit_prenum(e, expected_type);
    } else if (is_typed_expr(e)) {
        return visit_typed_expr(e);
    } else if (is_rec_fn_macro(e)) {
        // TODO(Leo)
        lean_unreachable();
    } else {
        buffer<expr> args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            args.push_back(visit(macro_arg(e, i), none_expr()));
        return update_macro(e, args.size(), args.data());
    }
}

expr elaborator::visit_lambda(expr const & e, optional<expr> const & expected_type) {
    // TODO(Leo)
    lean_unreachable();
}

expr elaborator::visit_pi(expr const & e, optional<expr> const & expected_type) {
    // TODO(Leo)
    lean_unreachable();
}

expr elaborator::visit_let(expr const & e, optional<expr> const & expected_type) {
    // TODO(Leo)
    lean_unreachable();
}

expr elaborator::visit(expr const & e, optional<expr> const & expected_type) {
    switch (e.kind()) {
    case expr_kind::Var:        lean_unreachable();  // LCOV_EXCL_LINE
    case expr_kind::Meta:       return e;
    case expr_kind::Sort:       return visit_sort(e);
    case expr_kind::Local:      return visit_local(e, expected_type);
    case expr_kind::Constant:   return visit_constant(e, expected_type);
    case expr_kind::Macro:      return visit_macro(e, expected_type);
    case expr_kind::Lambda:     return visit_lambda(e, expected_type);
    case expr_kind::Pi:         return visit_pi(e, expected_type);
    case expr_kind::App:        return visit_app(e, expected_type);
    case expr_kind::Let:        return visit_let(e, expected_type);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

std::tuple<expr, level_param_names> elaborator::operator()(expr const & e) {
    expr r = visit(e,  none_expr());
    // TODO(Leo)
    level_param_names ls;
    return std::make_tuple(r, ls);
}

std::tuple<expr, level_param_names> elaborate(environment const & env, options const & opts, local_level_decls const & lls,
                                              metavar_context const & mctx, local_context const & lctx, expr const & e) {
    return elaborator(env, opts, lls, mctx, lctx)(e);
}
}
