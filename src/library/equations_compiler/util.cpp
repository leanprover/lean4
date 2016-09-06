/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/find_fn.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/private.h"
#include "library/constants.h"
#include "library/annotation.h"
#include "library/replace_visitor.h"
#include "library/aux_definition.h"
#include "library/scope_pos_info_provider.h"
#include "library/compiler/vm_compiler.h"
#include "library/tactic/defeq_simplifier/defeq_simplifier.h"
#include "library/equations_compiler/equations.h"
#include "library/equations_compiler/util.h"

#ifndef LEAN_DEFAULT_EQN_COMPILER_DSIMP
#define LEAN_DEFAULT_EQN_COMPILER_DSIMP true
#endif

namespace lean {
static name * g_eqn_compiler_dsimp = nullptr;

static bool get_eqn_compiler_dsimp(options const & o) {
    return o.get_bool(*g_eqn_compiler_dsimp, LEAN_DEFAULT_EQN_COMPILER_DSIMP);
}

[[ noreturn ]] void throw_ill_formed_eqns() {
    throw exception("ill-formed match/equations expression");
}

static optional<pair<expr, unsigned>> get_eqn_fn_and_arity(expr e) {
    while (is_lambda(e))
        e = binding_body(e);
    if (!is_equation(e) && !is_no_equation(e)) throw_ill_formed_eqns();
    if (is_no_equation(e)) {
        return optional<pair<expr, unsigned>>();
    } else {
        expr const & lhs = equation_lhs(e);
        expr const & fn  = get_app_fn(lhs);
        lean_assert(is_local(fn));
        return optional<pair<expr, unsigned>>(fn, get_app_num_args(lhs));
    }
}

static expr consume_fn_prefix(expr eq, buffer<expr> const & fns) {
    for (unsigned i = 0; i < fns.size(); i++) {
        if (!is_lambda(eq)) throw_ill_formed_eqns();
        eq = binding_body(eq);
    }
    return instantiate_rev(eq, fns);
}

unpack_eqns::unpack_eqns(type_context & ctx, expr const & e):
    m_locals(ctx) {
    lean_assert(is_equations(e));
    m_src = e;
    buffer<expr> eqs;
    unsigned num_fns = equations_num_fns(e);
    to_equations(e, eqs);
    /* Extract functions. */
    lean_assert(eqs.size() > 0);
    expr eq = eqs[0];
    for (unsigned i = 0; i < num_fns; i++) {
        if (!is_lambda(eq)) throw_ill_formed_eqns();
        if (!closed(binding_domain(eq))) throw_ill_formed_eqns();
        m_fns.push_back(m_locals.push_local(binding_name(eq), binding_domain(eq)));
        eq = binding_body(eq);
    }
    /* Extract equations */
    unsigned eqidx = 0;
    for (unsigned fidx = 0; fidx < num_fns; fidx++) {
        m_eqs.push_back(buffer<expr>());
        buffer<expr> & fn_eqs = m_eqs.back();
        if (eqidx >= eqs.size()) throw_ill_formed_eqns();
        expr eq = consume_fn_prefix(eqs[eqidx], m_fns);
        fn_eqs.push_back(eq);
        eqidx++;
        if (auto p = get_eqn_fn_and_arity(eq)) {
            if (p->first != m_fns[fidx]) throw_ill_formed_eqns();
            unsigned arity = p->second;
            m_arity.push_back(arity);
            while (eqidx < eqs.size()) {
                expr eq = consume_fn_prefix(eqs[eqidx], m_fns);
                if (auto p = get_eqn_fn_and_arity(eq)) {
                    if (p->first == m_fns[fidx]) {
                        if (p->second != arity) throw_ill_formed_eqns();
                        fn_eqs.push_back(eq);
                        eqidx++;
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
        } else {
            /* noequation, guess arity using type of function */
            expr type = ctx.infer(m_fns[fidx]);
            unsigned arity = 0;
            while (is_pi(type)) {
                arity++;
                type = binding_body(type);
            }
            if (arity == 0) throw_ill_formed_eqns();
            m_arity.push_back(arity);
        }
    }
    if (eqs.size() != eqidx) throw_ill_formed_eqns();
    lean_assert(m_arity.size() == m_fns.size());
    lean_assert(m_eqs.size() == m_fns.size());
}

expr unpack_eqns::update_fn_type(unsigned fidx, expr const & type) {
    expr new_fn = m_locals.push_local(local_pp_name(m_fns[fidx]), type);
    m_fns[fidx] = new_fn;
    return new_fn;
}

expr unpack_eqns::repack() {
    buffer<expr> new_eqs;
    for (buffer<expr> const & fn_eqs : m_eqs) {
        for (expr const & eq : fn_eqs) {
            new_eqs.push_back(m_locals.ctx().mk_lambda(m_fns, eq));
        }
    }
    return update_equations(m_src, new_eqs);
}

unpack_eqn::unpack_eqn(type_context & ctx, expr const & eqn):
    m_src(eqn), m_locals(ctx) {
    expr it = eqn;
    while (is_lambda(it)) {
        expr d = instantiate_rev(binding_domain(it), m_locals.as_buffer().size(), m_locals.as_buffer().data());
        m_vars.push_back(m_locals.push_local(binding_name(it), d, binding_info(it)));
        it = binding_body(it);
    }
    it = instantiate_rev(it, m_locals.as_buffer().size(), m_locals.as_buffer().data());
    if (!is_equation(it)) throw_ill_formed_eqns();
    m_nested_src = it;
    m_lhs = equation_lhs(it);
    m_rhs = equation_rhs(it);
}

expr unpack_eqn::add_var(name const & n, expr const & type) {
    m_modified_vars = true;
    m_vars.push_back(m_locals.push_local(n, type));
    return m_vars.back();
}

expr unpack_eqn::repack() {
    if (!m_modified_vars &&
        equation_lhs(m_nested_src) == m_lhs &&
        equation_rhs(m_nested_src) == m_rhs) return m_src;
    expr new_eq = copy_tag(m_nested_src, mk_equation(m_lhs, m_rhs));
    return copy_tag(m_src, m_locals.ctx().mk_lambda(m_vars, new_eq));
}

bool is_recursive_eqns(type_context & ctx, expr const & e) {
    unpack_eqns ues(ctx, e);
    for (unsigned fidx = 0; fidx < ues.get_num_fns(); fidx++) {
        buffer<expr> const & eqns = ues.get_eqns_of(fidx);
        for (expr const & eqn : eqns) {
            expr it = eqn;
            while (is_lambda(it)) {
                it = binding_body(it);
            }
            if (!is_equation(it) && !is_no_equation(it)) throw_ill_formed_eqns();
            if (is_equation(it)) {
                expr const & rhs = equation_rhs(it);
                if (find(rhs, [&](expr const & e, unsigned) {
                            if (is_local(e)) {
                                for (unsigned fidx = 0; fidx < ues.get_num_fns(); fidx++) {
                                    if (mlocal_name(e) == mlocal_name(ues.get_fn(fidx)))
                                        return true;
                                }
                            }
                            return false;
                        })) {
                    return true;
                }
            }
        }
    }
    return false;
}

static pair<environment, name> mk_def_name(environment const & env, bool is_private, name const & c) {
    if (is_private) {
        unsigned h = 31;
        if (auto pinfo = get_pos_info_provider()) {
            h = hash(pinfo->get_some_pos().first, pinfo->get_some_pos().second);
            char const * fname = pinfo->get_file_name();
            h = hash_str(strlen(fname), fname, h);
        }
        return add_private_name(env, c, optional<unsigned>(h));
    } else {
        return mk_pair(env, c);
    }
}

pair<environment, expr> mk_aux_definition(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                          bool is_private, name const & c, expr const & type, expr const & value) {
    environment new_env = env;
    name new_c;
    std::tie(new_env, new_c) = mk_def_name(env, is_private, c);
    expr r;
    std::tie(new_env, r) = mk_aux_definition(new_env, mctx, lctx, new_c, type, value);
    try {
        declaration d = new_env.get(new_c);
        new_env = vm_compile(new_env, d);
    } catch (exception & ex) {
        throw nested_exception(sstream() << "equation compiler failed to generate bytecode for "
                               << "auxiliary declaration '" << c << "'", ex);
    }
    return mk_pair(new_env, r);
}

static unsigned g_eqn_sanitizer_token;

environment mk_equation_lemma(environment const & env, options const & opts, metavar_context const & mctx, local_context const & lctx,
                              bool is_private, name const & c, expr const & type, expr const & value) {
    environment new_env = env;
    name new_c;
    std::tie(new_env, new_c) = mk_def_name(env, is_private, c);
    expr r;
    expr new_type  = type;
    bool use_dsimp = get_eqn_compiler_dsimp(opts);
    if (use_dsimp) {
        try {
            type_context ctx(env, opts, mctx, lctx, transparency_mode::None);
            defeq_simp_lemmas_ptr lemmas = get_defeq_simp_lemmas(env, g_eqn_sanitizer_token);
            new_type = defeq_simplify(ctx, *lemmas, type);
        } catch (defeq_simplifier_exception & ex) {
            throw nested_exception("equation compiler failed to simplify type of automatically generated lemma using "
                                   "defeq simplifier "
                                   "(possible solution: disable simplification step using `set_option eqn_compiler.dsimp false`), "
                                   "defeq simplifier error message:\n", ex);
        }
    }
    std::tie(new_env, r) = mk_aux_definition(new_env, mctx, lctx, new_c, new_type, value);
    return new_env;
}

class erase_inaccessible_annotations_fn : public replace_visitor {
    virtual expr visit_macro(expr const & e) override {
        if (is_inaccessible(e)) {
            return visit(get_annotation_arg(e));
        } else {
            return replace_visitor::visit_macro(e);
        }
    }
};

expr erase_inaccessible_annotations(expr const & e) {
    return erase_inaccessible_annotations_fn()(e);
}

list<expr> erase_inaccessible_annotations(list<expr> const & es) {
    return map(es, [&](expr const & e) { return erase_inaccessible_annotations(e); });
}


static expr whnf_ite(type_context & ctx, expr const & e) {
    return ctx.whnf_pred(e, [&](expr const & e) {
            expr const & fn = get_app_fn(e);
            return !is_constant(fn, get_ite_name());
        });
}

/* Return true iff `lhs` is of the form (@ite (x = y) s A t e).
   If the result is true, then the ite args are stored in `ite_args`. */
static bool is_ite_eq(expr const & lhs, buffer<expr> & ite_args) {
    expr const & fn = get_app_args(lhs, ite_args);
    return is_constant(fn, get_ite_name()) && ite_args.size() == 5 && is_eq(ite_args[0]);
}

/* Try to find (H : not c) at Hs */
static optional<expr> find_if_neg_hypothesis(type_context & ctx, expr const & c, buffer<expr> const & Hs) {
    for (expr const & H : Hs) {
        expr H_type = ctx.infer(H);
        expr arg;
        if (is_not(ctx.env(), H_type, arg) && ctx.is_def_eq(c, arg)) {
            return some_expr(H);
        }
    }
    return none_expr();
}

static expr prove_eqn_lemma_core(type_context & ctx, buffer<expr> const & Hs, expr const & lhs, expr const & rhs) {
    buffer<expr> ite_args;
    expr new_lhs = whnf_ite(ctx, lhs);
    if (is_ite_eq(new_lhs, ite_args)) {
        expr const & c = ite_args[0];
        expr c_lhs, c_rhs;
        lean_verify(is_eq(c, c_lhs, c_rhs));
        if (ctx.is_def_eq(c_lhs, c_rhs)) {
            expr H = mk_eq_refl(ctx, c_lhs);
            expr lhs_then = ite_args[3];
            expr A        = ite_args[2];
            level A_lvl   = get_level(ctx, A);
            expr H1       = mk_app(mk_constant(get_if_pos_name(), {A_lvl}), {c, ite_args[1], H, A, lhs_then, ite_args[4]});
            expr H2       = prove_eqn_lemma_core(ctx, Hs, lhs_then, rhs);
            expr eq_trans = mk_constant(get_eq_trans_name(), {A_lvl});
            return mk_app(eq_trans, {A, lhs, lhs_then, rhs, H1, H2});
        } else if (auto H = find_if_neg_hypothesis(ctx, c, Hs)) {
            expr lhs_else = ite_args[4];
            expr A        = ite_args[2];
            level A_lvl   = get_level(ctx, A);
            expr H1       = mk_app(mk_constant(get_if_neg_name(), {A_lvl}), {c, ite_args[1], *H, A, ite_args[3], lhs_else});
            expr H2       = prove_eqn_lemma_core(ctx, Hs, lhs_else, rhs);
            return mk_app(mk_constant(get_eq_trans_name(), {A_lvl}), {A, lhs, lhs_else, rhs, H1, H2});
        }
    }

    if (ctx.is_def_eq(lhs, rhs)) {
        return mk_eq_refl(ctx, rhs);
    }

    /* TODO(Leo): add support for pack/unpack lemmas */

    throw exception("equation compiler failed to prove equation lemma (workaround: "
                    "disable lemma generation using `set_option eqn_compiler.lemmas false`)");
}

expr prove_eqn_lemma(type_context & ctx, buffer<expr> const & Hs, expr const & lhs, expr const & rhs) {
    expr body = prove_eqn_lemma_core(ctx, Hs, lhs, rhs);
    return ctx.mk_lambda(Hs, body);
}


void initialize_eqn_compiler_util() {
    g_eqn_compiler_dsimp = new name{"eqn_compiler", "dsimp"};
    register_bool_option(*g_eqn_compiler_dsimp, LEAN_DEFAULT_EQN_COMPILER_DSIMP,
                         "(equation compiler) use defeq simplifier to cleanup types of "
                         "automatically synthesized equational lemmas");
    g_eqn_sanitizer_token = register_defeq_simp_attribute("eqn_sanitizer");
}

void finalize_eqn_compiler_util() {
    delete g_eqn_compiler_dsimp;
}
}
