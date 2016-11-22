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
#include "library/app_builder.h"
#include "library/private.h"
#include "library/constants.h"
#include "library/annotation.h"
#include "library/inverse.h"
#include "library/num.h"
#include "library/string.h"
#include "library/replace_visitor.h"
#include "library/aux_definition.h"
#include "library/comp_val.h"
#include "library/scope_pos_info_provider.h"
#include "library/compiler/vm_compiler.h"
#include "library/tactic/eqn_lemmas.h"
#include "library/equations_compiler/equations.h"
#include "library/equations_compiler/util.h"

#ifndef LEAN_DEFAULT_EQN_COMPILER_LEMMAS
#define LEAN_DEFAULT_EQN_COMPILER_LEMMAS true
#endif

#ifndef LEAN_DEFAULT_EQN_COMPILER_ZETA
#define LEAN_DEFAULT_EQN_COMPILER_ZETA false
#endif

namespace lean {
static name * g_eqn_compiler_lemmas = nullptr;
static name * g_eqn_compiler_zeta   = nullptr;

static bool get_eqn_compiler_lemmas(options const & o) {
    return o.get_bool(*g_eqn_compiler_lemmas, LEAN_DEFAULT_EQN_COMPILER_LEMMAS);
}

static bool get_eqn_compiler_zeta(options const & o) {
    return o.get_bool(*g_eqn_compiler_zeta, LEAN_DEFAULT_EQN_COMPILER_ZETA);
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

bool has_inaccessible_annotation(expr const & e) {
    return static_cast<bool>(find(e, [&](expr const & e, unsigned) { return is_inaccessible(e); }));
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
    if (has_inaccessible_annotation(e))
        return erase_inaccessible_annotations_fn()(e);
    else
        return e;
}

list<expr> erase_inaccessible_annotations(list<expr> const & es) {
    return map(es, [&](expr const & e) { return erase_inaccessible_annotations(e); });
}

local_context erase_inaccessible_annotations(local_context const & lctx) {
    local_context r;
    r.m_next_idx = lctx.m_next_idx;
    lctx.m_idx2local_decl.for_each([&](unsigned, local_decl const & d) {
            expr new_type = erase_inaccessible_annotations(d.get_type());
            optional<expr> new_value;
            if (auto val = d.get_value())
                new_value = erase_inaccessible_annotations(*val);
            auto new_d = local_context::update_local_decl(d, new_type, new_value);
            r.m_name2local_decl.insert(d.get_name(), new_d);
            r.m_idx2local_decl.insert(d.get_idx(), new_d);
            r.insert_user_name(d);
        });
    return r;
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

static void throw_mk_aux_definition_error(local_context const & lctx, name const & c, expr const & type, expr const & value, exception & ex) {
    sstream strm;
    strm << "equation compiler failed to create auxiliary declaration '" << c << "'";
    if (contains_let_local_decl(lctx, type) || contains_let_local_decl(lctx, value)) {
        strm << ", auxiliary declaration has references to let-declarations (possible solution: use 'set_option eqn_compiler.zeta true')";
    }
    throw nested_exception(strm, ex);
}

pair<environment, expr> mk_aux_definition(environment const & env, options const & opts, metavar_context const & mctx, local_context const & lctx,
                                          equations_header const & header, name const & c, expr const & type, expr const & value) {
    lean_trace("eqn_compiler", tout() << "declaring auxiliary definition\n" << c << " : " << type << "\n";);
    environment new_env = env;
    expr new_type       = type;
    expr new_value      = value;
    bool zeta           = get_eqn_compiler_zeta(opts);
    if (zeta) {
        new_type  = zeta_expand(lctx, new_type);
        new_value = zeta_expand(lctx, new_value);
    }
    name new_c;
    std::tie(new_env, new_c) = mk_def_name(env, header.m_is_private, c);
    expr r;
    try {
        std::tie(new_env, r) = header.m_is_lemma ?
            mk_aux_lemma(new_env, mctx, lctx, new_c, new_type, new_value) :
            mk_aux_definition(new_env, mctx, lctx, new_c, new_type, new_value);
    } catch (exception & ex) {
        throw_mk_aux_definition_error(lctx, c, new_type, new_value, ex);
    }
    if (!header.m_is_lemma && !header.m_is_noncomputable) {
        try {
            declaration d = new_env.get(new_c);
            new_env = vm_compile(new_env, d);
        } catch (exception & ex) {
            if (!header.m_prev_errors) {
                throw nested_exception(sstream() << "equation compiler failed to generate bytecode for "
                                       << "auxiliary declaration '" << c << "'", ex);
            }
        }
    }
    return mk_pair(new_env, r);
}

static environment add_equation_lemma(environment const & env, options const & opts, metavar_context const & mctx, local_context const & lctx,
                                      bool is_private, name const & c, expr const & type, expr const & value) {
    environment new_env = env;
    name new_c;
    std::tie(new_env, new_c) = mk_def_name(env, is_private, c);
    expr r;
    expr new_type  = type;
    expr new_value = value;
    bool zeta      = get_eqn_compiler_zeta(opts);
    if (zeta) {
        new_type   = zeta_expand(lctx, new_type);
        new_value  = zeta_expand(lctx, new_value);
    }
    try {
        std::tie(new_env, r) = mk_aux_definition(new_env, mctx, lctx, new_c, new_type, new_value);
        if (is_rfl_lemma(new_type, new_value))
            new_env = mark_rfl_lemma(new_env, new_c);
        new_env = add_eqn_lemma(new_env, new_c);
    } catch (exception & ex) {
        throw_mk_aux_definition_error(lctx, c, new_type, new_value, ex);
    }
    return new_env;
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

static bool conservative_is_def_eq(type_context & ctx, expr const & a, expr const & b) {
    type_context::transparency_scope scope(ctx, transparency_mode::Reducible);
    return ctx.is_def_eq(a, b);
}

static lbool compare_values(expr const & a, expr const & b) {
    if (auto v1 = to_num(a)) {
    if (auto v2 = to_num(b)) {
        return to_lbool(*v1 == *v2);
    }}

    if (auto v1 = to_char(a)) {
    if (auto v2 = to_char(b)) {
        return to_lbool(*v1 == *v2);
    }}

    if (auto v1 = to_string(a)) {
    if (auto v2 = to_string(b)) {
        return to_lbool(*v1 == *v2);
    }}

    return l_undef;
}

static optional<expr> mk_val_ne_proof(type_context & ctx, expr const & a, expr const & b) {
    expr type = ctx.infer(a);
    if (ctx.is_def_eq(type, mk_constant(get_nat_name())))
        return mk_nat_val_ne_proof(a, b);
    if (ctx.is_def_eq(type, mk_constant(get_char_name())))
        return mk_char_val_ne_proof(a, b);
    if (ctx.is_def_eq(type, mk_constant(get_string_name())))
        return mk_string_val_ne_proof(a, b);
    return none_expr();
}

static bool quick_is_def_eq_when_values(type_context & ctx, expr const & a, expr const & b) {
    if (!is_local(a) && !is_local(b)) {
        if (compare_values(a, b) == l_true)
            return true;
    }
    return conservative_is_def_eq(ctx, a, b);
}

/* Try to find (H : not (c_lhs = c_rhs)) at Hs */
static optional<expr> find_if_neg_hypothesis(type_context & ctx, expr const & c_lhs, expr const & c_rhs,
                                             buffer<expr> const & Hs) {
    for (expr const & H : Hs) {
        expr H_type = ctx.infer(H);
        expr arg, arg_lhs, arg_rhs;
        if (is_not(H_type, arg) && is_eq(arg, arg_lhs, arg_rhs) &&
            quick_is_def_eq_when_values(ctx, arg_lhs, c_lhs) &&
            quick_is_def_eq_when_values(ctx, arg_rhs, c_rhs)) {
            return some_expr(H);
        }
    }
    return none_expr();
}

/*
  If `e` is of the form

      (@eq.rec B (f (g (f a))) C (h (g (f a))) (f a) (f_g_eq (f a))

  such that

      f_g_eq : forall x, f (g x) = x

  and there is a lemma

      g_f_eq : forall x, g (f x) = x

  Return (h a) and a proof that (e = h a)

  The proof is of the form

  @eq.rec
     A
     a
     (fun x : A, (forall H : f x = f a, @eq.rec B (f x) C (h x) (f a) H = h a))
     (fun H : f a = f a, eq.refl (h a))
     (g (f a))
     (eq.symm (g_f_eq a))
     (f_g_eq a)
*/
static optional<expr_pair> prove_eq_rec_invertible(type_context & ctx, expr const & e) {
    buffer<expr> rec_args;
    expr rec_fn = get_app_args(e, rec_args);
    if (!is_constant(rec_fn, get_eq_rec_name()) || rec_args.size() != 6) return optional<expr_pair>();
    expr B      = rec_args[0];
    expr from   = rec_args[1]; /* (f (g (f a))) */
    expr C      = rec_args[2];
    expr minor  = rec_args[3]; /* (h (g (f a))) */
    expr to     = rec_args[4]; /* (f a) */
    expr major  = rec_args[5]; /* (f_g_eq (f a)) */
    if (!is_app(from) || !is_app(minor)) return optional<expr_pair>();
    if (!ctx.is_def_eq(app_arg(from), app_arg(minor))) return optional<expr_pair>();
    expr h     = app_fn(minor);
    expr g_f_a = app_arg(from);
    if (!is_app(g_f_a) || !ctx.is_def_eq(app_arg(g_f_a), to)) return optional<expr_pair>();
    expr g     = get_app_fn(g_f_a);
    if (!is_constant(g)) return optional<expr_pair>();
    expr f_a   = to;
    if (!is_app(f_a)) return optional<expr_pair>();
    expr f     = get_app_fn(f_a);
    expr a     = app_arg(f_a);
    if (!is_constant(f)) return optional<expr_pair>();
    optional<inverse_info> info = has_inverse(ctx.env(), const_name(f));
    if (!info || info->m_inv != const_name(g)) return optional<expr_pair>();
    name g_f_name = info->m_lemma;
    optional<inverse_info> info_inv = has_inverse(ctx.env(), const_name(g));
    if (!info_inv || info_inv->m_inv != const_name(f)) return optional<expr_pair>();
    buffer<expr> major_args;
    expr f_g_eq = get_app_args(major, major_args);
    if (!is_constant(f_g_eq) || major_args.empty() || !ctx.is_def_eq(f_a, major_args.back())) return optional<expr_pair>();
    if (const_name(f_g_eq) != info_inv->m_lemma) return optional<expr_pair>();

    expr A          = ctx.infer(a);
    level A_lvl     = get_level(ctx, A);
    expr h_a        = mk_app(h, a);
    expr refl_h_a   = mk_eq_refl(ctx, h_a);
    expr f_a_eq_f_a = mk_eq(ctx, f_a, f_a);
    /* (fun H : f a = f a, eq.refl (h a)) */
    expr pr_minor   = mk_lambda("_H", f_a_eq_f_a, refl_h_a);
    type_context::tmp_locals aux_locals(ctx);
    expr x          = aux_locals.push_local("_x", A);
    /* Remark: we cannot use mk_app(f, x) in the following line.
       Reason: f may have implicit arguments. So, app_fn(f_x) is not equal to f in general,
       and app_fn(f_a) is f + implicit arguments. */
    expr f_x        = mk_app(app_fn(f_a), x);
    expr f_x_eq_f_a = mk_eq(ctx, f_x, f_a);
    expr H          = aux_locals.push_local("_H", f_x_eq_f_a);
    expr h_x        = mk_app(h, x);
    /* (@eq.rec B (f x) C (h x) (f a) H) */
    expr eq_rec2    = mk_app(rec_fn, {B, f_x, C, h_x, f_a, H});
    /* (@eq.rec B (f x) C (h x) (f a) H) = h a */
    expr eq_rec2_eq = mk_eq(ctx, eq_rec2, h_a);
    /* (fun x : A, (forall H : f x = f a, @eq.rec B (f x) C (h x) (f a) H = h a)) */
    expr pr_motive  = ctx.mk_lambda(x, ctx.mk_pi(H, eq_rec2_eq));
    expr g_f_eq_a   = mk_app(ctx, g_f_name, a);
    /* (eq.symm (g_f_eq a)) */
    expr pr_major   = mk_eq_symm(ctx, g_f_eq_a);
    expr pr         = mk_app(mk_constant(get_eq_rec_name(), {mk_level_zero(), A_lvl}),
                             {A, a, pr_motive, pr_minor, g_f_a, pr_major, major});

    return optional<expr_pair>(mk_pair(h_a, pr));
}

static expr prove_eqn_lemma_core(type_context & ctx, buffer<expr> const & Hs, expr const & lhs, expr const & rhs) {
    buffer<expr> ite_args;
    expr new_lhs = whnf_ite(ctx, lhs);
    if (is_ite_eq(new_lhs, ite_args)) {
        expr const & c = ite_args[0];
        expr c_lhs, c_rhs;
        lean_verify(is_eq(c, c_lhs, c_rhs));
        if (auto H = find_if_neg_hypothesis(ctx, c_lhs, c_rhs, Hs)) {
            expr lhs_else = ite_args[4];
            expr A        = ite_args[2];
            level A_lvl   = get_level(ctx, A);
            expr H1       = mk_app(mk_constant(get_if_neg_name(), {A_lvl}), {c, ite_args[1], *H, A, ite_args[3], lhs_else});
            expr H2       = prove_eqn_lemma_core(ctx, Hs, lhs_else, rhs);
            return mk_app(mk_constant(get_eq_trans_name(), {A_lvl}), {A, lhs, lhs_else, rhs, H1, H2});
        } else if (quick_is_def_eq_when_values(ctx, c_lhs, c_rhs)) {
            expr H = mk_eq_refl(ctx, c_lhs);
            expr lhs_then = ite_args[3];
            expr A        = ite_args[2];
            level A_lvl   = get_level(ctx, A);
            expr H1       = mk_app(mk_constant(get_if_pos_name(), {A_lvl}), {c, ite_args[1], H, A, lhs_then, ite_args[4]});
            expr H2       = prove_eqn_lemma_core(ctx, Hs, lhs_then, rhs);
            expr eq_trans = mk_constant(get_eq_trans_name(), {A_lvl});
            return mk_app(eq_trans, {A, lhs, lhs_then, rhs, H1, H2});
        } else if (compare_values(c_lhs, c_rhs) == l_false) {
            if (auto H = mk_val_ne_proof(ctx, c_lhs, c_rhs)) {
                expr lhs_else = ite_args[4];
                expr A        = ite_args[2];
                level A_lvl   = get_level(ctx, A);
                expr H1       = mk_app(mk_constant(get_if_neg_name(), {A_lvl}), {c, ite_args[1], *H, A, ite_args[3], lhs_else});
                expr H2       = prove_eqn_lemma_core(ctx, Hs, lhs_else, rhs);
                return mk_app(mk_constant(get_eq_trans_name(), {A_lvl}), {A, lhs, lhs_else, rhs, H1, H2});
            }
        }
    }

    if (optional<expr_pair> p = prove_eq_rec_invertible(ctx, new_lhs)) {
        expr new_new_lhs = p->first;
        expr H1          = p->second;
        expr H2          = prove_eqn_lemma_core(ctx, Hs, new_new_lhs, rhs);
        return mk_eq_trans(ctx, H1, H2);
    }

    if (ctx.is_def_eq(lhs, rhs)) {
        return mk_eq_refl(ctx, rhs);
    }

    throw exception("equation compiler failed to prove equation lemma (workaround: "
                    "disable lemma generation using `set_option eqn_compiler.lemmas false`)");
}

static expr prove_eqn_lemma(type_context & ctx, buffer<expr> const & Hs, expr const & lhs, expr const & rhs) {
    expr body = prove_eqn_lemma_core(ctx, Hs, lhs, rhs);
    return ctx.mk_lambda(Hs, body);
}

environment mk_equation_lemma(environment const & env, options const & opts, metavar_context const & mctx, local_context const & lctx,
                              name const & f_name, unsigned eqn_idx, bool is_private,
                              buffer<expr> const & Hs, expr const & lhs, expr const & rhs) {
    if (!get_eqn_compiler_lemmas(opts)) return env;
    type_context ctx(env, opts, mctx, lctx, transparency_mode::Semireducible);
    expr type     = ctx.mk_pi(Hs, mk_eq(ctx, lhs, rhs));
    expr proof    = prove_eqn_lemma(ctx, Hs, lhs, rhs);
    name eqn_name = name(name(f_name, "equations"), "eqn").append_after(eqn_idx);
    return add_equation_lemma(env, opts, mctx, lctx, is_private, eqn_name, type, proof);
}

void initialize_eqn_compiler_util() {
    register_trace_class("eqn_compiler");
    register_trace_class(name{"debug", "eqn_compiler"});
    g_eqn_compiler_lemmas = new name{"eqn_compiler", "lemmas"};
    g_eqn_compiler_zeta   = new name{"eqn_compiler", "zeta"};
    register_bool_option(*g_eqn_compiler_lemmas, LEAN_DEFAULT_EQN_COMPILER_LEMMAS,
                         "(equation compiler) generate equation lemmas and induction principle");
    register_bool_option(*g_eqn_compiler_zeta, LEAN_DEFAULT_EQN_COMPILER_ZETA,
                         "(equation compiler) apply zeta-expansion (expand references to let-declarations) before creating auxiliary definitions.");
}

void finalize_eqn_compiler_util() {
    delete g_eqn_compiler_lemmas;
    delete g_eqn_compiler_zeta;
}
}
