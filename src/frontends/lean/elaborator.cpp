/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <functional>
#include <utility>
#include <vector>
#include "util/flet.h"
#include "util/list_fn.h"
#include "util/lazy_list_fn.h"
#include "util/sstream.h"
#include "util/name_map.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/kernel_exception.h"
#include "kernel/error_msgs.h"
#include "kernel/free_vars.h"
#include "kernel/inductive/inductive.h"
#include "library/coercion.h"
#include "library/placeholder.h"
#include "library/choice.h"
#include "library/explicit.h"
#include "library/reducible.h"
#include "library/locals.h"
#include "library/let.h"
#include "library/sorry.h"
#include "library/flycheck.h"
#include "library/deep_copy.h"
#include "library/typed_expr.h"
#include "library/metavar_closure.h"
#include "library/local_context.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/choice_iterator.h"
#include "library/projection.h"
#include "library/pp_options.h"
#include "library/class_instance_synth.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/error_handling/error_handling.h"
#include "library/definitional/equations.h"
#include "frontends/lean/local_decls.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/tactic_hint.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/info_annotation.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/calc_proof_elaborator.h"
#include "frontends/lean/info_tactic.h"
#include "frontends/lean/begin_end_ext.h"
#include "frontends/lean/elaborator_exception.h"
#include "frontends/lean/nested_declaration.h"
#include "frontends/lean/calc.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/opt_cmd.h"

namespace lean {
type_checker_ptr mk_coercion_from_type_checker(environment const & env, name_generator && ngen) {
    auto irred_pred = mk_irreducible_pred(env);
    return mk_type_checker(env, std::move(ngen), [=](name const & n) {
            return has_coercions_from(env, n) || irred_pred(n);
        });
}

type_checker_ptr mk_coercion_to_type_checker(environment const & env, name_generator && ngen) {
    auto irred_pred = mk_irreducible_pred(env);
    return mk_type_checker(env, std::move(ngen), [=](name const & n) {
            return has_coercions_to(env, n) || irred_pred(n);
        });
}

/** \brief 'Choice' expressions <tt>(choice e_1 ... e_n)</tt> are mapped into a metavariable \c ?m
    and a choice constraints <tt>(?m in fn)</tt> where \c fn is a choice function.
    The choice function produces a stream of alternatives. In this case, it produces a stream of
    size \c n, one alternative for each \c e_i.
    This is a helper class for implementing this choice functions.
*/
struct elaborator::choice_expr_elaborator : public choice_iterator {
    elaborator &  m_elab;
    local_context m_context;
    local_context m_full_context;
    bool          m_in_equation_lhs;
    expr          m_meta;
    expr          m_type;
    expr          m_choice;
    unsigned      m_idx;

    choice_expr_elaborator(elaborator & elab, local_context const & ctx, local_context const & full_ctx, bool in_equation_lhs,
                           expr const & meta, expr const & type, expr const & c):
        m_elab(elab), m_context(ctx), m_full_context(full_ctx), m_in_equation_lhs(in_equation_lhs), m_meta(meta),
        m_type(type), m_choice(c), m_idx(get_num_choices(m_choice)) {
    }

    virtual optional<constraints> next() {
        while (m_idx > 0) {
            --m_idx;
            expr const & c = get_choice(m_choice, m_idx);
            expr const & f = get_app_fn(c);
            m_elab.save_identifier_info(f);
            try {
                flet<local_context> set1(m_elab.m_context,         m_context);
                flet<local_context> set2(m_elab.m_full_context,    m_full_context);
                flet<bool>          set3(m_elab.m_in_equation_lhs, m_in_equation_lhs);
                pair<expr, constraint_seq> rcs = m_elab.visit(c);
                expr r                         = rcs.first;
                constraint_seq cs              = rcs.second;
                if (!has_expr_metavar_relaxed(m_type)) {
                    // we only try coercions here if the m_type and r_type do not contain metavariables.
                    constraint_seq new_cs      = cs;
                    expr r_type                = m_elab.infer_type(r, new_cs);
                    if (!has_expr_metavar_relaxed(r_type)) {
                        cs = new_cs;
                        auto new_rcs                   = m_elab.ensure_has_type(r, r_type, m_type, justification());
                        r                              = new_rcs.first;
                        cs                            += new_rcs.second;
                    }
                }
                cs = mk_eq_cnstr(m_meta, r, justification()) + cs;
                return optional<constraints>(cs.to_list());
            } catch (exception &) {}
        }
        return optional<constraints>();
    }
};

elaborator::elaborator(elaborator_context & ctx, name_generator && ngen, bool nice_mvar_names):
    m_ctx(ctx),
    m_ngen(ngen),
    m_context(),
    m_full_context(),
    m_unifier_config(ctx.m_ios.get_options(), true /* use exceptions */, true /* discard */) {
    m_has_sorry = has_sorry(m_ctx.m_env);
    m_use_tactic_hints  = true;
    m_no_info           = false;
    m_in_equation_lhs   = false;
    m_tc                = mk_type_checker(ctx.m_env, m_ngen.mk_child());
    m_coercion_from_tc  = mk_coercion_from_type_checker(ctx.m_env, m_ngen.mk_child());
    m_coercion_to_tc    = mk_coercion_to_type_checker(ctx.m_env, m_ngen.mk_child());
    m_nice_mvar_names   = nice_mvar_names;
}

expr elaborator::mk_local(name const & n, expr const & t, binder_info const & bi) {
    return ::lean::mk_local(m_ngen.next(), n, t, bi);
}

void elaborator::register_meta(expr const & meta) {
    lean_assert(is_meta(meta));
    name const & n = mlocal_name(get_app_fn(meta));
    m_mvar2meta.insert(n, meta);
}

/** \brief Convert the metavariable to the metavariable application that captures
    the context where it was defined.
*/
optional<expr> elaborator::mvar_to_meta(expr const & mvar) {
    lean_assert(is_metavar(mvar));
    name const & m = mlocal_name(mvar);
    if (auto it = m_mvar2meta.find(m))
        return some_expr(*it);
    else
        return none_expr();
}

/** \brief Store the pair (pos(e), type(r)) in the info_data if m_info_manager is available. */
void elaborator::save_type_data(expr const & e, expr const & r) {
    if (!m_no_info && infom() && pip() &&
        (is_constant(e) || is_local(e) || is_placeholder(e) || is_as_atomic(e) ||
         is_consume_args(e) || is_notation_info(e))) {
        if (auto p = pip()->get_pos_info(e)) {
            expr t = m_tc->infer(r).first;
            m_pre_info_data.add_type_info(p->first, p->second, t);
        }
    }
}

/** \brief Store the pair (pos(e), r) in the info_data if m_info_manager is available. */
void elaborator::save_binder_type(expr const & e, expr const & r) {
    if (!m_no_info && infom() && pip()) {
        if (auto p = pip()->get_pos_info(e)) {
            m_pre_info_data.add_type_info(p->first, p->second, r);
        }
    }
}

/** \brief Store type information at pos(e) for r if \c e is marked as "extra" in the info_manager */
void elaborator::save_extra_type_data(expr const & e, expr const & r) {
    if (!m_no_info && infom() && pip()) {
        if (auto p = pip()->get_pos_info(e)) {
            expr t = m_tc->infer(r).first;
            m_pre_info_data.add_extra_type_info(p->first, p->second, r, t);
        }
    }
}

/** \brief Store proof_state information at pos(e) in the info_manager */
void elaborator::save_proof_state_info(proof_state const & ps, expr const & e) {
    if (!m_no_info && infom() && pip()) {
        if (auto p = pip()->get_pos_info(e)) {
            m_pre_info_data.add_proof_state_info(p->first, p->second, ps);
        }
    }
}

/** \brief Auxiliary function for saving information about which overloaded identifier was used by the elaborator. */
void elaborator::save_identifier_info(expr const & f) {
    if (!m_no_info && infom() && pip() && is_constant(f)) {
        if (auto p = pip()->get_pos_info(f))
            m_pre_info_data.add_identifier_info(p->first, p->second, const_name(f));
    }
}

/** \brief Store actual term that was synthesized for an explicit placeholders */
void elaborator::save_synth_data(expr const & e, expr const & r) {
    if (!m_no_info && infom() && pip() && is_placeholder(e)) {
        if (auto p = pip()->get_pos_info(e))
            m_pre_info_data.add_synth_info(p->first, p->second, r);
    }
}

void elaborator::save_placeholder_info(expr const & e, expr const & r) {
    if (is_explicit_placeholder(e)) {
        save_type_data(e, r);
        save_synth_data(e, r);
    }
    unsigned line, col;
    if (m_ctx.has_show_hole_at(line, col)) {
        if (auto p = pip()->get_pos_info(e)) {
            if (p->first == line && p->second == col) {
                m_to_show_hole = r;
                m_to_show_hole_ref = e;
                m_ctx.reset_show_goal_at();
            }
        }
    }
}

/** \brief Auxiliary function for saving information about which coercion was used by the elaborator.
    It marks that coercion c was used on e.
*/
void elaborator::save_coercion_info(expr const & e, expr const & c) {
    if (!m_no_info && infom() && pip()) {
        if (auto p = pip()->get_pos_info(e)) {
            expr t = m_tc->infer(c).first;
            m_pre_info_data.add_coercion_info(p->first, p->second, c, t);
        }
    }
}

/** \brief Remove coercion information associated with \c e */
void elaborator::erase_coercion_info(expr const & e) {
    if (!m_no_info && infom() && pip()) {
        if (auto p = pip()->get_pos_info(e))
            m_pre_info_data.erase_coercion_info(p->first, p->second);
    }
}

void elaborator::instantiate_info(substitution s) {
    if (m_to_show_hole) {
        expr meta      = s.instantiate(*m_to_show_hole);
        expr meta_type = s.instantiate(type_checker(env()).infer(meta).first);
        goal g(meta, meta_type);
        proof_state ps(goals(g), s, m_ngen, constraints());
        auto out = regular(env(), ios());
        print_lean_info_header(out.get_stream());
        out << ps.pp(env(), ios()) << endl;
        print_lean_info_footer(out.get_stream());
    }
    if (infom()) {
        m_pre_info_data.instantiate(s);
        bool overwrite = true;
        infom()->merge(m_pre_info_data, overwrite);
        m_pre_info_data.clear();
    }
}

optional<name> elaborator::mk_mvar_suffix(expr const & b) {
    if (!infom() && !m_nice_mvar_names)
        return optional<name>();
    else
        return optional<name>(binding_name(b));
}

/** \brief Create a metavariable, and attach choice constraint for generating
    solutions using class-instances and tactic-hints.
*/
expr elaborator::mk_placeholder_meta(optional<name> const & suffix, optional<expr> const & type,
                                     tag g, bool is_strict, bool is_inst_implicit, constraint_seq & cs) {
    if (is_inst_implicit && !m_ctx.m_ignore_instances) {
        auto ec = mk_class_instance_elaborator(
            env(), ios(), m_context, m_ngen.next(), suffix,
            use_local_instances(), is_strict, type, g, m_unifier_config, m_ctx.m_pos_provider);
        register_meta(ec.first);
        cs += ec.second;
        return ec.first;
    } else {
        expr m = m_context.mk_meta(m_ngen, suffix, type, g);
        register_meta(m);
        return m;
    }
}

expr elaborator::visit_expecting_type(expr const & e, constraint_seq & cs) {
    if (is_placeholder(e) && !placeholder_type(e)) {
        expr r = m_context.mk_type_meta(m_ngen, e.get_tag());
        save_placeholder_info(e, r);
        return r;
    } else if (is_no_info(e)) {
        flet<bool> let(m_no_info, true);
        return visit_expecting_type(get_annotation_arg(e), cs);
    } else {
        return visit(e, cs);
    }
}

expr elaborator::visit_expecting_type_of(expr const & e, expr const & t, constraint_seq & cs) {
    if (is_placeholder(e) && !placeholder_type(e)) {
        bool inst_imp = true;
        expr r = mk_placeholder_meta(some_expr(t), e.get_tag(), is_strict_placeholder(e), inst_imp, cs);
        save_placeholder_info(e, r);
        return r;
    } else if (is_no_info(e)) {
        flet<bool> let(m_no_info, true);
        return visit_expecting_type_of(get_annotation_arg(e), t, cs);
    } else if (is_choice(e)) {
        return visit_choice(e, some_expr(t), cs);
    } else if (is_by(e)) {
        return visit_by(e, some_expr(t), cs);
    } else if (is_by_plus(e)) {
        return visit_by_plus(e, some_expr(t), cs);
    } else if (is_calc_annotation(e)) {
        return visit_calc_proof(e, some_expr(t), cs);
    } else {
        return visit(e, cs);
    }
}

expr elaborator::visit_choice(expr const & e, optional<expr> const & t, constraint_seq & cs) {
    lean_assert(is_choice(e));
    // Possible optimization: try to lookahead and discard some of the alternatives.
    expr m                 = m_full_context.mk_meta(m_ngen, t, e.get_tag());
    register_meta(m);
    local_context ctx      = m_context;
    local_context full_ctx = m_full_context;
    bool in_equation_lhs   = m_in_equation_lhs;
    auto fn = [=](expr const & meta, expr const & type, substitution const & /* s */,
                  name_generator && /* ngen */) {
        return choose(std::make_shared<choice_expr_elaborator>(*this, ctx, full_ctx, in_equation_lhs, meta, type, e));
    };
    auto pp_fn = [=](formatter const & fmt, pos_info_provider const * pos_prov, substitution const &, bool is_main, bool) {
        format r = pp_previous_error_header(fmt, pos_prov, some_expr(e), is_main);
        r += format("none of the overloads is applicable:");
        for (unsigned i = 0; i < get_num_choices(e); i++) {
            expr const & c = get_choice(e, i);
            expr const & f = get_app_fn(c);
            optional<name> fn;
            if (is_constant(f))
                fn = const_name(f);
            else if (is_local(f))
                fn = local_pp_name(f);
            r += space();
            if (fn) {
                r += format(*fn);
            } else {
                r += format("[nontrivial]");
            }
        }
        return r;
    };
    justification j = mk_justification(some_expr(e), pp_fn);
    cs += mk_choice_cnstr(m, fn, to_delay_factor(cnstr_group::Basic), true, j);
    return m;
}

expr elaborator::visit_by(expr const & e, optional<expr> const & t, constraint_seq & cs) {
    lean_assert(is_by(e));
    expr tac = visit(get_by_arg(e), cs);
    expr m   = m_context.mk_meta(m_ngen, t, e.get_tag());
    register_meta(m);
    m_local_tactic_hints.insert(mlocal_name(get_app_fn(m)), tac);
    return m;
}

expr elaborator::visit_by_plus(expr const & e, optional<expr> const & t, constraint_seq & cs) {
    lean_assert(is_by_plus(e));
    expr tac = visit(get_by_plus_arg(e), cs);
    expr m   = m_full_context.mk_meta(m_ngen, t, e.get_tag());
    register_meta(m);
    m_local_tactic_hints.insert(mlocal_name(get_app_fn(m)), tac);
    return m;
}

expr elaborator::visit_calc_proof(expr const & e, optional<expr> const & t, constraint_seq & cs) {
    lean_assert(is_calc_annotation(e));
    info_manager * im = nullptr;
    if (infom())
        im = &m_pre_info_data;
    pair<expr, constraint_seq> ecs = visit(get_annotation_arg(e));
    expr m                         = m_full_context.mk_meta(m_ngen, t, e.get_tag());
    register_meta(m);
    auto fn = [=](expr const & t) { save_type_data(get_annotation_arg(e), t); };
    constraint c                   = mk_calc_proof_cnstr(env(), ios().get_options(),
                                                         m_context, m, ecs.first, ecs.second, m_unifier_config,
                                                         im, fn);
    cs += c;
    return m;
}

static bool is_implicit_pi(expr const & e) {
    if (!is_pi(e))
        return false;
    binder_info bi = binding_info(e);
    return bi.is_strict_implicit() || bi.is_implicit() || bi.is_inst_implicit();
}

/** \brief Auxiliary function for adding implicit arguments to coercions to function-class */
expr elaborator::add_implict_args(expr e, constraint_seq & cs) {
    type_checker & tc = *m_tc;
    constraint_seq new_cs;
    expr type = tc.whnf(tc.infer(e, new_cs), new_cs);
    if (!is_implicit_pi(type))
        return e;
    cs += new_cs;
    while (true) {
        lean_assert(is_pi(type));
        tag g = e.get_tag();
        bool is_strict = true;
        bool inst_imp  = binding_info(type).is_inst_implicit();
        expr imp_arg   = mk_placeholder_meta(mk_mvar_suffix(type), some_expr(binding_domain(type)),
                                             g, is_strict, inst_imp, cs);
        e              = mk_app(e, imp_arg, g);
        type           = instantiate(binding_body(type), imp_arg);
        constraint_seq new_cs;
        type           = tc.whnf(type, new_cs);
        if (!is_implicit_pi(type))
            return e;
        cs += new_cs;
    }
}

static expr mk_coercion_app(expr const & coe, expr const & a) {
    if (is_inaccessible(a))
        return copy_tag(a, mk_inaccessible(mk_app(coe, get_annotation_arg(a), a.get_tag())));
    else
        return mk_app(coe, a, a.get_tag());
}

/** \brief Make sure \c f is really a function, if it is not, try to apply coercions.
    The result is a pair <tt>new_f, f_type</tt>, where new_f is the new value for \c f,
    and \c f_type is its type (and a Pi-expression)
*/
pair<expr, expr> elaborator::ensure_fun(expr f, constraint_seq & cs) {
    expr f_type = infer_type(f, cs);
    expr saved_f_type       = f_type;
    constraint_seq saved_cs = cs;
    if (!is_pi(f_type))
        f_type = whnf(f_type, cs);
    if (is_pi(f_type)) {
        erase_coercion_info(f);
    } else {
        if (m_tc->is_stuck(f_type)) {
            f_type = m_tc->ensure_pi(f_type, f, cs);
            erase_coercion_info(f);
        } else {
            cs     = saved_cs;
            f_type = m_coercion_from_tc->whnf(saved_f_type, cs);
            // try coercion to function-class
            list<expr> coes  = get_coercions_to_fun(env(), f_type);
            if (is_nil(coes)) {
                throw_kernel_exception(env(), f, [=](formatter const & fmt) { return pp_function_expected(fmt, f); });
            } else if (is_nil(tail(coes))) {
                expr old_f = f;
                f = mk_coercion_app(head(coes), f);
                f = add_implict_args(f, cs);
                f_type = infer_type(f, cs);
                save_coercion_info(old_f, f);
                lean_assert(is_pi(f_type));
            } else {
                local_context ctx      = m_context;
                local_context full_ctx = m_full_context;
                justification j        = mk_justification(f, [=](formatter const & fmt, substitution const & subst, bool) {
                        return pp_function_expected(fmt, substitution(subst).instantiate(f));
                    });
                auto choice_fn = [=](expr const & meta, expr const &, substitution const &, name_generator &&) {
                    flet<local_context> save1(m_context,      ctx);
                    flet<local_context> save2(m_full_context, full_ctx);
                    list<constraints> choices = map2<constraints>(coes, [&](expr const & coe) {
                            expr new_f      = mk_coercion_app(coe, f);
                            constraint_seq cs;
                            new_f = add_implict_args(new_f, cs);
                            cs += mk_eq_cnstr(meta, new_f, j);
                            return cs.to_list();
                        });
                    return choose(std::make_shared<coercion_elaborator>(*this, f, choices, coes, false));
                };
                f   = m_full_context.mk_meta(m_ngen, none_expr(), f.get_tag());
                register_meta(f);
                cs += mk_choice_cnstr(f, choice_fn, to_delay_factor(cnstr_group::Basic), true, j);
                lean_assert(is_meta(f));
                // let type checker add constraint
                f_type = infer_type(f, cs);
                f_type = m_tc->ensure_pi(f_type, f, cs);
                lean_assert(is_pi(f_type));
            }
        }
    }
    lean_assert(is_pi(f_type));
    return mk_pair(f, f_type);
}

bool elaborator::has_coercions_from(expr const & a_type, bool & lifted_coe) {
    try {
        expr a_cls  = get_app_fn(m_coercion_from_tc->whnf(a_type).first);
        if (m_ctx.m_lift_coercions) {
            while (is_pi(a_cls)) {
                expr local = mk_local(binding_name(a_cls), binding_domain(a_cls), binding_info(a_cls));
                a_cls      = get_app_fn(m_coercion_from_tc->whnf(instantiate(binding_body(a_cls), local)).first);
                lifted_coe = true;
            }
        }
        return is_constant(a_cls) && ::lean::has_coercions_from(env(), const_name(a_cls));
    } catch (exception&) {
        return false;
    }
}

bool elaborator::has_coercions_to(expr d_type) {
    try {
        d_type = m_coercion_to_tc->whnf(d_type).first;
        expr const & fn = get_app_fn(d_type);
        if (is_constant(fn))
            return ::lean::has_coercions_to(env(), const_name(fn));
        else if (is_pi(d_type))
            return ::lean::has_coercions_to_fun(env());
        else if (is_sort(d_type))
            return ::lean::has_coercions_to_sort(env());
        else
            return false;
    } catch (exception&) {
        return false;
    }
}

expr elaborator::apply_coercion(expr const & a, expr a_type, expr d_type) {
    a_type = m_coercion_from_tc->whnf(a_type).first;
    d_type = m_coercion_to_tc->whnf(d_type).first;
    constraint_seq aux_cs;
    list<expr> coes = get_coercions_from_to(*m_coercion_from_tc, *m_coercion_to_tc, a_type, d_type, aux_cs, m_ctx.m_lift_coercions);
    if (is_nil(coes)) {
        erase_coercion_info(a);
        return a;
    } else if (is_nil(tail(coes))) {
        expr r = mk_coercion_app(head(coes), a);
        save_coercion_info(a, r);
        return r;
    } else {
        for (expr const & coe : coes) {
            expr r = mk_coercion_app(coe, a);
            expr r_type = infer_type(r).first;
            try {
                if (m_tc->is_def_eq(r_type, d_type).first) {
                    save_coercion_info(a, r);
                    return r;
                }
            } catch (exception&) {
            }
        }
        erase_coercion_info(a);
        return a;
    }
}

/** \brief Given a term <tt>a : a_type</tt>, and an expected type generate a metavariable with a delayed coercion. */
pair<expr, constraint_seq> elaborator::mk_delayed_coercion(
    expr const & a, expr const & a_type, expr const & expected_type,
    justification const & j) {
    expr m       = m_full_context.mk_meta(m_ngen, some_expr(expected_type), a.get_tag());
    register_meta(m);
    constraint c = mk_coercion_cnstr(*m_coercion_from_tc, *m_coercion_to_tc, *this, m, a, a_type, j,
                                     to_delay_factor(cnstr_group::Basic), m_ctx.m_lift_coercions);
    return to_ecs(m, c);
}

/** \brief Given a term <tt>a : a_type</tt>, ensure it has type \c expected_type. Apply coercions if needed */
pair<expr, constraint_seq> elaborator::ensure_has_type_core(
    expr const & a, expr const & a_type, expr const & expected_type, bool use_expensive_coercions, justification const & j) {
    bool lifted_coe = false;
    if (use_expensive_coercions &&
        has_coercions_from(a_type, lifted_coe) && ((!lifted_coe && is_meta(expected_type)) || (lifted_coe && is_pi_meta(expected_type)))) {
        return mk_delayed_coercion(a, a_type, expected_type, j);
    } else if (use_expensive_coercions && !m_in_equation_lhs && is_meta(a_type) && has_coercions_to(expected_type)) {
        return mk_delayed_coercion(a, a_type, expected_type, j);
    } else {
        pair<bool, constraint_seq> dcs;
        try {
            dcs = m_tc->is_def_eq(a_type, expected_type, j);
        } catch (exception&) {
            dcs.first = false;
        }
        if (dcs.first) {
            return to_ecs(a, dcs.second);
        } else {
            expr new_a = apply_coercion(a, a_type, expected_type);
            constraint_seq cs;
            bool coercion_worked = false;
            if (!is_eqp(a, new_a)) {
                expr new_a_type = infer_type(new_a, cs);
                try {
                    coercion_worked = m_tc->is_def_eq(new_a_type, expected_type, j, cs);
                } catch (exception&) {
                    coercion_worked = false;
                }
            }
            if (coercion_worked) {
                return to_ecs(new_a, cs);
            } else if (has_metavar(a_type) || has_metavar(expected_type)) {
                // rely on unification hints to solve this constraint
                return to_ecs(a, mk_eq_cnstr(a_type, expected_type, j));
            } else {
                throw unifier_exception(j, substitution());
            }
        }
    }
}

bool elaborator::is_choice_app(expr const & e) {
    expr const & f = get_app_fn(e);
    return is_choice(f) || (is_annotation(f) && is_choice(get_nested_annotation_arg(f)));
}

/** \brief Process ((choice f_1 ... f_n) a_1 ... a_k) as
    (choice (f_1 a_1 ... a_k) ... (f_n a_1 ... a_k))
*/
expr elaborator::visit_choice_app(expr const & e, constraint_seq & cs) {
    buffer<expr> args;
    expr r = get_app_rev_args(e, args);
    expr f = get_nested_annotation_arg(r);
    lean_assert(is_choice(f));
    buffer<expr> new_choices;
    unsigned num = get_num_choices(f);
    for (unsigned i = 0; i < num; i++) {
        expr f_i = get_choice(f, i);
        f_i      = copy_annotations(r, f_i);
        new_choices.push_back(mk_rev_app(f_i, args));
    }
    return visit_choice(copy_tag(e, mk_choice(new_choices.size(), new_choices.data())), none_expr(), cs);
}

expr elaborator::visit_app(expr const & e, constraint_seq & cs) {
    if (is_choice_app(e))
        return visit_choice_app(e, cs);
    constraint_seq f_cs;
    bool expl   = is_nested_explicit(get_app_fn(e));
    expr f      = visit(app_fn(e), f_cs);
    auto f_t    = ensure_fun(f, f_cs);
    f           = f_t.first;
    expr f_type = f_t.second;
    lean_assert(is_pi(f_type));
    if (!expl) {
        bool first = true;
        while (binding_info(f_type).is_strict_implicit() ||
               (!first && binding_info(f_type).is_implicit()) ||
               (!first && binding_info(f_type).is_inst_implicit())) {
            tag g          = f.get_tag();
            bool is_strict = true;
            bool inst_imp  = binding_info(f_type).is_inst_implicit();
            expr imp_arg   = mk_placeholder_meta(mk_mvar_suffix(f_type), some_expr(binding_domain(f_type)),
                                                 g, is_strict, inst_imp, f_cs);
            f              = mk_app(f, imp_arg, g);
            auto f_t       = ensure_fun(f, f_cs);
            f              = f_t.first;
            f_type         = f_t.second;
            first          = false;
        }
        if (!first) {
            // we save the info data again for application of functions with strict implicit arguments
            save_type_data(get_app_fn(e), f);
        }
    }
    constraint_seq a_cs;
    expr d_type = binding_domain(f_type);
    if (d_type == get_tactic_expr_type() || d_type == get_tactic_identifier_type() ||
        d_type == get_tactic_using_expr_type()) {
        expr const & a = app_arg(e);
        expr r;
        if (is_local(a) &&
            (mlocal_type(a) == get_tactic_expr_type()
             || mlocal_type(a) == get_tactic_identifier_type()
             || m_in_equation_lhs)) {
            r = mk_app(f, a, e.get_tag());
        } else {
            r = mk_app(f, mk_tactic_expr(a), e.get_tag());
        }
        cs += f_cs + a_cs;
        return r;
    } else {
        expr a          = visit_expecting_type_of(app_arg(e), d_type, a_cs);
        expr a_type     = infer_type(a, a_cs);
        expr r          = mk_app(f, a, e.get_tag());
        justification j = mk_app_justification(r, f_type, a, a_type);
        // If the application is an equations expression, then we are compiling a match-with, and expensive
        // coercions should not be considered.
        bool use_expensive_coercions = !is_equations(app_fn(e));
        auto new_a_cs   = ensure_has_type_core(a, a_type, d_type, use_expensive_coercions, j);
        expr new_a      = new_a_cs.first;
        cs += f_cs + new_a_cs.second + a_cs;
        return update_app(r, app_fn(r), new_a);
    }
}

expr elaborator::visit_placeholder(expr const & e, constraint_seq & cs) {
    bool inst_implicit = true;
    expr r = mk_placeholder_meta(placeholder_type(e), e.get_tag(), is_strict_placeholder(e), inst_implicit, cs);
    save_placeholder_info(e, r);
    return r;
}

level elaborator::replace_univ_placeholder(level const & l) {
    auto fn = [&](level const & l) {
        if (is_placeholder(l))
            return some_level(mk_meta_univ(m_ngen.next()));
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

expr elaborator::visit_sort(expr const & e) {
    expr r = update_sort(e, replace_univ_placeholder(sort_level(e)));
    if (contains_placeholder(sort_level(e)))
        m_to_check_sorts.emplace_back(e, r);
    return r;
}

expr elaborator::visit_macro(expr const & e, constraint_seq & cs) {
    if (is_as_is(e)) {
        return get_as_is_arg(e);
    } else {
        buffer<expr> args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            args.push_back(visit(macro_arg(e, i), cs));
        return update_macro(e, args.size(), args.data());
    }
}

expr elaborator::visit_constant(expr const & e) {
    declaration d = env().get(const_name(e));
    buffer<level> ls;
    for (level const & l : const_levels(e))
        ls.push_back(replace_univ_placeholder(l));
    unsigned num_univ_params = d.get_num_univ_params();
    if (num_univ_params < ls.size())
        throw_kernel_exception(env(), sstream() << "incorrect number of universe levels parameters for '"
                               << const_name(e) << "', #" << num_univ_params
                               << " expected, #" << ls.size() << " provided");
    // "fill" with meta universe parameters
    for (unsigned i = ls.size(); i < num_univ_params; i++)
        ls.push_back(mk_meta_univ(m_ngen.next()));
    lean_assert(num_univ_params == ls.size());
    return update_constant(e, to_list(ls.begin(), ls.end()));
}

/** \brief Make sure \c e is a type. If it is not, then try to apply coercions. */
expr elaborator::ensure_type(expr const & e, constraint_seq & cs) {
    expr t = infer_type(e, cs);
    erase_coercion_info(e);
    if (is_sort(t))
        return e;
    expr            saved_t = t;
    constraint_seq saved_cs = cs;
    t = whnf(t, cs);
    if (is_sort(t))
        return e;
    if (has_metavar(t)) {
        t = whnf(t, cs);
        if (is_sort(t))
            return e;
        if (is_meta(t)) {
            // let type checker add constraint
            m_tc->ensure_sort(t, e, cs);
            return e;
        }
    }
    cs = saved_cs;
    t  = m_coercion_from_tc->whnf(saved_t, cs);
    list<expr> coes = get_coercions_to_sort(env(), t);
    if (is_nil(coes)) {
        throw_kernel_exception(env(), e, [=](formatter const & fmt) { return pp_type_expected(fmt, e); });
    } else {
        // Remark: we ignore other coercions to sort
        expr r = mk_coercion_app(head(coes), e);
        save_coercion_info(e, r);
        return r;
    }
}

/** \brief Similar to instantiate_rev, but assumes that subst contains only local constants.
    When replacing a variable with a local, we copy the local constant and inherit the tag
    associated with the variable. This is a trick for getter better error messages */
expr elaborator::instantiate_rev_locals(expr const & a, unsigned n, expr const * subst) {
    if (closed(a))
        return a;
    auto fn = [=](expr const & m, unsigned offset) -> optional<expr> {
        if (offset >= get_free_var_range(m))
            return some_expr(m); // expression m does not contain free variables with idx >= offset
        if (is_var(m)) {
            unsigned vidx = var_idx(m);
            if (vidx >= offset) {
                unsigned h = offset + n;
                if (h < offset /* overflow, h is bigger than any vidx */ || vidx < h) {
                    expr local = subst[n - (vidx - offset) - 1];
                    lean_assert(is_local(local));
                    return some_expr(copy_tag(m, copy(local)));
                } else {
                    return some_expr(copy_tag(m, mk_var(vidx - n)));
                }
            }
        }
        return none_expr();
    };
    return replace(a, fn);
}

expr elaborator::visit_binding(expr e, expr_kind k, constraint_seq & cs) {
    flet<local_context> save1(m_context, m_context);
    flet<local_context> save2(m_full_context, m_full_context);
    buffer<expr> ds, ls, es;
    while (e.kind() == k) {
        es.push_back(e);
        expr const & d0 = binding_domain(e);
        expr d          = d0;
        d = instantiate_rev_locals(d, ls.size(), ls.data());
        d = ensure_type(visit_expecting_type(d, cs), cs);

        if (is_placeholder(d0) && !is_explicit_placeholder(d0))
            save_binder_type(d0, d);

        ds.push_back(d);
        expr l   = mk_local(binding_name(e), d, binding_info(e));
        if (!is_match_binder_name(binding_name(e))) {
            if (binding_info(e).is_contextual())
                m_context.add_local(l);
            m_full_context.add_local(l);
        }
        ls.push_back(l);
        e = binding_body(e);
    }
    lean_assert(ls.size() == es.size() && ls.size() == ds.size());
    e = instantiate_rev_locals(e, ls.size(), ls.data());
    e = (k == expr_kind::Pi) ? ensure_type(visit_expecting_type(e, cs), cs) : visit(e, cs);
    e = abstract_locals(e, ls.size(), ls.data());
    unsigned i = ls.size();
    while (i > 0) {
        --i;
        e = update_binding(es[i], abstract_locals(ds[i], i, ls.data()), e);
    }
    return e;
}
expr elaborator::visit_pi(expr const & e, constraint_seq & cs) {
    return visit_binding(e, expr_kind::Pi, cs);
}
expr elaborator::visit_lambda(expr const & e, constraint_seq & cs) {
    return visit_binding(e, expr_kind::Lambda, cs);
}

expr elaborator::visit_typed_expr(expr const & e, constraint_seq & cs) {
    constraint_seq t_cs;
    expr t      = visit(get_typed_expr_type(e), t_cs);
    constraint_seq v_cs;
    expr v      = visit_expecting_type_of(get_typed_expr_expr(e), t, v_cs);
    expr v_type = infer_type(v, v_cs);
    justification j = mk_type_mismatch_jst(v, v_type, t, e);
    auto new_vcs    = ensure_has_type(v, v_type, t, j);
    v = new_vcs.first;
    cs += t_cs + new_vcs.second + v_cs;
    return v;
}

expr elaborator::visit_let_value(expr const & e, constraint_seq & cs) {
    if (auto p = m_cache.find(e)) {
        cs += p->second;
        return p->first;
    } else {
        auto ecs = visit(get_let_value_expr(e));
        expr r = copy_tag(ecs.first, mk_let_value(ecs.first));
        m_cache.insert(e, mk_pair(r, ecs.second));
        cs += ecs.second;
        return r;
    }
}

bool elaborator::is_sorry(expr const & e) const {
    return m_has_sorry && ::lean::is_sorry(e);
}

expr elaborator::visit_sorry(expr const & e) {
    level u = mk_meta_univ(m_ngen.next());
    expr t  = mk_sort(u);
    expr m  = m_full_context.mk_meta(m_ngen, some_expr(t), e.get_tag());
    return mk_app(update_constant(e, to_list(u)), m, e.get_tag());
}

expr const & elaborator::get_equation_fn(expr const & eq) const {
    expr it = eq;
    while (is_lambda(it))
        it = binding_body(it);
    if (!is_equation(it))
        throw_elaborator_exception("ill-formed equation", eq);
    expr const & fn = get_app_fn(equation_lhs(it));
    if (!is_local(fn))
        throw_elaborator_exception("ill-formed equation", eq);
    return fn;
}

/**
   \brief Given two binding expressions \c source and \c target
   s.t. they have at least \c num binders, replace the first \c num binders of \c target with \c source.
   The binder types are wrapped with \c mk_as_is to make sure the elaborator will not process
   them again.
*/
static expr copy_domain(unsigned num, expr const & source, expr const & target) {
    if (num == 0) {
        return target;
    } else {
        lean_assert(is_binding(source) && is_binding(target));
        return update_binding(source, mk_as_is(binding_domain(source)),
                              copy_domain(num-1, binding_body(source), binding_body(target)));
    }
}


enum lhs_meta_kind { None, Accessible, Inaccessible };

/**
   \brief Auxiliary function for searching for metavariable (applications) on the left-hand-side (lhs) of equations.
   The possible results are:
      - None: lhs does not contain meta-variables
      - Accessible: lhs contains meta-variable, and it is located in a position considered by the pattern-matcher.
      - Inaccessible: lhs contains meta-variable, and it is located in a possible inaccessible/ignored by the pattern-matcher,
                      or its type also contains meta-variables

   \remark If the lhs contains accessible and inaccessible metavariables, an accessible is returned.
*/
static pair<lhs_meta_kind, expr> find_lhs_meta(type_checker & tc, expr const & e) {
    if (!has_metavar(e))
        return mk_pair(None, expr());
    environment const & env = tc.env();
    optional<expr> acc, inacc;
    std::function<void(expr const &, bool)> visit = [&](expr const & e, bool accessible) {
        if (acc || !has_metavar(e)) {
            return; // done
        } else if (is_inaccessible(e)) {
            visit(get_annotation_arg(e), false);
        } else if (is_meta(e)) {
            if (accessible && !acc) {
                expr type = tc.infer(e).first;
                if (!has_expr_metavar_strict(type))
                    acc = e;
                else if (!inacc)
                    inacc = e;
            } else if (!accessible && !inacc) {
                inacc = e;
            }
        } else if (is_app(e)) {
            if (!accessible) {
                visit(app_fn(e), false);
                visit(app_arg(e), false);
            } else {
                buffer<expr> args;
                expr const & fn = get_app_args(e, args);
                if (is_constant(fn) && inductive::is_intro_rule(env, const_name(fn))) {
                    name I              = *inductive::is_intro_rule(env, const_name(fn));
                    unsigned num_params = *inductive::get_num_params(env, I);
                    for (unsigned i = 0; i < num_params; i++)
                        visit(args[i], false);
                    for (unsigned i = num_params; i < args.size(); i++)
                        visit(args[i], accessible);
                } else {
                    visit(fn, false);
                    for (expr const & arg : args)
                        visit(arg, false);
                }
            }
        } else if (is_macro(e)) {
            for (unsigned i = 0; i < macro_num_args(e); i++)
                visit(macro_arg(e, i), false);
        } else if (is_binding(e)) {
            visit(binding_domain(e), false);
            visit(binding_body(e), false);
        }
    };
    buffer<expr> args;
    get_app_args(e, args);
    for (expr const & arg : args)
        visit(arg, true);
    if (acc)
        return mk_pair(Accessible, *acc);
    else if (inacc)
        return mk_pair(Inaccessible, *inacc);
    else
        return mk_pair(None, expr());
}

/**
   \brief The left-hand-side of recursive equations may contain metavariables associated with
   implicit parameters. This procedure replaces them with fresh local constants.

   \remark only "accessible" metavariables are replaced

   Example 1)
   Suppose we are defining
   map : Pi {n}, vec A n -> vec B n -> vec C n,
   map nil nil             := nil,
   map (a :: va) (b :: vb) := f a b :: map va vb

   After elaboration the second equation will be

   @map (succ ?M) (@cons A ?M a va) (@cons A ?M b vb) := @cons A ?M (f ab) (@map ?M va vb)

   This procedure replaces ?M with (x_1 : nat), where x_1 is a new local constant.
   The resultant eqns object is:
   [equations
     (λ (map : Π {n : ℕ}, vector A n → vector B n → vector C n), [equation (map nil nil) nil])
     (λ (map : Π {n : ℕ}, vector A n → vector B n → vector C n) (a : A) (x_1 : ℕ) (va : vector A x_1) (b : B)
        (vb : vector B x_1),
          [equation (map (a :: va) (b :: vb)) (f a b :: map va vb)])]


   Example 2)
   Suppose we are defining
   definition ideq : Π {A : Type} {a b : A}, a = b → a = b,
   ideq H := H

   After elaboration the equation is:
   @ideq ?M1 ?M2 ?M3 H := H

   This procedure replaces ?M1 ?M2 ?M3 with
   (x_1 : Type) (x_2 : x_1) (x_3 : x_1)
   The resultant eqns object is

   [equations
    (λ (ideq : ∀ {A : Type} {a b : A}, @eq A a b → @eq A a b) (x_1 : Type) (x_2 x_3 : x_1) (H : @eq x_1 x_2 x_3),
       [equation (@ideq x_1 x_2 x_3 H) H])]
*/
static expr assign_equation_lhs_metas(type_checker & tc, expr const & eqns) {
    lean_assert(is_equations(eqns));
    if (!has_metavar(eqns))
        return eqns;
    buffer<expr> eqs;
    buffer<expr> new_eqs;
    to_equations(eqns, eqs);
    unsigned num_fns = equations_num_fns(eqns);

    auto replace_meta = [](expr const & e, expr const & meta, expr const & local) {
        expr mvar = get_app_fn(meta);
        return replace(e, [&](expr const & e, unsigned) {
                if (is_meta(e) && mlocal_name(get_app_fn(e)) == mlocal_name(mvar)) {
                    return some_expr(local);
                } else if (!has_metavar(e)) {
                    return some_expr(e);
                } else {
                    return none_expr();
                }
            });
    };

    for (expr eq : eqs) {
        if (!has_metavar(eq)) {
            new_eqs.push_back(eq);
        } else {
            buffer<expr> locals;
            name_generator ngen = tc.mk_ngen();
            eq = fun_to_telescope(ngen, eq, locals, optional<binder_info>());
            if (is_equation(eq)) {
                name x("x");
                lean_assert(num_fns <= locals.size());
                lean_assert(is_equation(eq));
                unsigned idx = 1;
                while (true) {
                    expr lhs = equation_lhs(eq);
                    auto r = find_lhs_meta(tc, lhs);
                    if (r.first == None) {
                        break;
                    } else if (r.first == Accessible) {
                        expr const & meta = r.second;
                        expr meta_type    = tc.infer(meta).first;
                        expr new_local    = mk_local(tc.mk_fresh_name(), x.append_after(idx), meta_type, binder_info());
                        for (expr & local : locals)
                            local = update_mlocal(local, replace_meta(mlocal_type(local), meta, new_local));
                        eq  = replace_meta(eq, meta, new_local);
                        unsigned i = num_fns;
                        for (; i < locals.size(); i++) {
                            if (depends_on(mlocal_type(locals[i]), new_local))
                                break;
                        }
                        locals.insert(i, new_local);
                        idx++;
                    } else {
                        lean_assert(r.first == Inaccessible);
                        throw_elaborator_exception(eqns, [=](formatter const & fmt) {
                                options o = fmt.get_options().update_if_undef(get_pp_implicit_name(), true);
                                o = o.update_if_undef(get_pp_notation_option_name(), false);
                                formatter new_fmt = fmt.update_options(o);
                                expr const & f = get_app_fn(lhs);
                                format r;
                                if (is_local(f) && is_match_binder_name(local_pp_name(f))) {
                                    r = format("invalid 'match' expression, left-hand-side contains meta-variable");
                                    r += pp_indent_expr(new_fmt, app_arg(lhs));
                                } else {
                                    r = format("invalid recursive equation, left-hand-side contains meta-variable");
                                    r += format(" (possible solution: provide implicit parameters occurring in left-hand-side explicitly)");
                                    r += pp_indent_expr(new_fmt, lhs);
                                }
                                return r;
                            });
                    }
                }
            } else {
                lean_assert(is_no_equation(eq));
            }
            new_eqs.push_back(Fun(locals, eq));
        }
    }
    return update_equations(eqns, new_eqs);
}

// \remark original_eqns is eqns before elaboration
constraint elaborator::mk_equations_cnstr(expr const & m, expr const & eqns) {
    environment const & _env = env();
    io_state const & _ios    = ios();
    justification j          = mk_failed_to_synthesize_jst(_env, m);
    auto choice_fn = [=](expr const & meta, expr const & meta_type, substitution const & s,
                         name_generator && ngen) {
        substitution new_s  = s;
        expr new_eqns       = new_s.instantiate_all(eqns);
        new_eqns            = solve_unassigned_mvars(new_s, new_eqns);
        if (display_unassigned_mvars(new_eqns, new_s))
            return lazy_list<constraints>();
        type_checker_ptr tc = mk_type_checker(_env, std::move(ngen));
        new_eqns            = assign_equation_lhs_metas(*tc, new_eqns);
        expr val            = compile_equations(*tc, _ios, new_eqns, meta, meta_type);
        justification j     = mk_justification("equation compilation", some_expr(eqns));
        constraint c        = mk_eq_cnstr(meta, val, j);
        return lazy_list<constraints>(c);
    };
    bool owner = true;
    return mk_choice_cnstr(m, choice_fn, to_delay_factor(cnstr_group::MaxDelayed), owner, j);
}

expr elaborator::visit_equations(expr const & eqns, constraint_seq & cs) {
    buffer<expr> eqs;
    buffer<expr> new_eqs;
    optional<expr> new_R;
    optional<expr> new_Hwf;

    to_equations(eqns, eqs);

    if (eqs.empty())
        throw_elaborator_exception("invalid empty set of recursive equations", eqns);

    if (is_wf_equations(eqns)) {
        new_R   = visit(equations_wf_rel(eqns), cs);
        new_Hwf = visit(equations_wf_proof(eqns), cs);
        expr Hwf_type   = infer_type(*new_Hwf, cs);
        expr wf         = visit(mk_constant(get_well_founded_name()), cs);
        wf              = ::lean::mk_app(wf, *new_R);
        justification j = mk_type_mismatch_jst(*new_Hwf, Hwf_type, wf, equations_wf_proof(eqns));
        auto new_Hwf_cs = ensure_has_type(*new_Hwf, Hwf_type, wf, j);
        new_Hwf         = new_Hwf_cs.first;
        cs             += new_Hwf_cs.second;
    }

    flet<optional<expr>> set1(m_equation_R, new_R);
    unsigned num_fns = equations_num_fns(eqns);

    optional<expr> first_eq;
    for (expr const & eq : eqs) {
        expr new_eq;
        constraint_seq new_cs;
        buffer<expr> fns_locals;
        fun_to_telescope(m_ngen, eq, fns_locals, optional<binder_info>());
        list<expr> locals = to_list(fns_locals.begin() + num_fns, fns_locals.end());
        if (first_eq) {
            // Replace first num_fns domains of eq with the ones in first_eq.
            // This is a trick/hack to ensure the fns in each equation have
            // the same elaborated type.
            new_eq = visit(copy_domain(num_fns, *first_eq, eq), new_cs);
        } else {
            new_eq = visit(eq, new_cs);
            first_eq = new_eq;
        }
        // To produce more helpful error messages, we decorate all
        // justifications created when processing eq with the list of local variables declared in the
        // left-hand-side of the equation.
        buffer<constraint> tmp_cs;
        new_cs.linearize(tmp_cs);
        for (constraint const & c : tmp_cs) {
            justification j = c.get_justification();
            auto pp_fn      = [=](formatter const & fmt, pos_info_provider const * pp, substitution const & s, bool is_main, bool) {
                if (!is_main)
                    return format();
                format r = j.pp(fmt, pp, s);
                r += compose(line(), format("The following identifier(s) are introduced as free variables by the "
                                            "left-hand-side of the equation:"));
                format aux;
                for (expr const & l : locals)
                    aux += compose(format(local_pp_name(l)), space());
                r += nest(get_pp_indent(fmt.get_options()), compose(line(), aux));
                return r;
            };
            justification new_j = mk_wrapper(j, j.get_main_expr(), pp_fn);
            cs += update_justification(c, new_j);
        }
        new_eqs.push_back(new_eq);
    }

    expr new_eqns;
    if (new_R) {
        new_eqns = copy_tag(eqns, mk_equations(num_fns, new_eqs.size(), new_eqs.data(), *new_R, *new_Hwf));
    } else {
        new_eqns = copy_tag(eqns, mk_equations(num_fns, new_eqs.size(), new_eqs.data()));
    }

    lean_assert(first_eq && is_lambda(*first_eq));
    expr type = binding_domain(*first_eq);
    expr m = m_full_context.mk_meta(m_ngen, some_expr(type), eqns.get_tag());
    register_meta(m);
    constraint c = mk_equations_cnstr(m, new_eqns);
    cs += c;
    return m;
}

expr elaborator::visit_equation(expr const & eq, constraint_seq & cs) {
    expr const & lhs = equation_lhs(eq);
    expr const & rhs = equation_rhs(eq);
    expr lhs_fn = get_app_fn(lhs);
    if (is_explicit(lhs_fn))
        lhs_fn = get_explicit_arg(lhs_fn);
    if (!is_local(lhs_fn))
        throw exception("ill-formed equation");
    expr new_lhs, new_rhs;
    {
        flet<bool> set(m_in_equation_lhs, true);
        new_lhs = visit(lhs, cs);
    }
    {
        optional<expr> some_new_lhs(new_lhs);
        flet<optional<expr>> set1(m_equation_lhs, some_new_lhs);
        new_rhs = visit(rhs, cs);
    }

    expr lhs_type = infer_type(new_lhs, cs);
    expr rhs_type = infer_type(new_rhs, cs);
    justification j = mk_justification(eq, [=](formatter const & fmt, substitution const & subst, bool as_error) {
            substitution s(subst);
            name n = local_pp_name(lhs_fn);
            if (is_match_binder_name(n))
                n = "match";
            return pp_def_type_mismatch(fmt, n, s.instantiate(lhs_type), s.instantiate(rhs_type), as_error);
        });
    pair<expr, constraint_seq> new_rhs_cs = ensure_has_type(new_rhs, rhs_type, lhs_type, j);
    new_rhs = new_rhs_cs.first;
    cs     += new_rhs_cs.second;
    return copy_tag(eq, mk_equation(new_lhs, new_rhs));
}

expr elaborator::visit_inaccessible(expr const & e, constraint_seq & cs) {
    if (!m_in_equation_lhs)
        throw_elaborator_exception("invalid occurrence of 'inaccessible' annotation, it must only occur in the "
                                   "left-hand-side of recursive equations", e);
    return mk_inaccessible(visit(get_annotation_arg(e), cs));
}

expr elaborator::visit_decreasing(expr const & e, constraint_seq & cs) {
    if (!m_equation_lhs)
        throw_elaborator_exception("invalid occurrence of 'decreasing' annotation, it must only occur in "
                                   "the right-hand-side of recursive equations", e);
    if (!m_equation_R)
        throw_elaborator_exception("invalid occurrence of 'decreasing' annotation, it can only be used when "
                                   "recursive equations are being defined by well-founded recursion", e);
    expr const & lhs_fn = get_app_fn(*m_equation_lhs);
    if (get_app_fn(decreasing_app(e)) != lhs_fn)
        throw_elaborator_exception("invalid occurrence of 'decreasing' annotation, expression must be an "
                                   "application of the recursive function being defined", e);
    expr dec_app        = visit(decreasing_app(e), cs);
    expr dec_proof      = visit(decreasing_proof(e), cs);
    expr f_type         = mlocal_type(get_app_fn(*m_equation_lhs));
    buffer<expr> ts;
    type_checker & tc = *m_tc;
    to_telescope(tc, f_type, ts, optional<binder_info>(), cs);
    buffer<expr> old_args;
    buffer<expr> new_args;
    get_app_args(*m_equation_lhs, old_args);
    get_app_args(dec_app, new_args);
    if (new_args.size() != old_args.size() || new_args.size() != ts.size())
        throw_elaborator_exception("invalid recursive application, mistmatch in the number of arguments", e);
    expr old_tuple  = mk_sigma_mk(tc, ts, old_args, cs);
    expr new_tuple  = mk_sigma_mk(tc, ts, new_args, cs);
    expr expected_dec_proof_type = mk_app(mk_app(*m_equation_R, new_tuple, e.get_tag()), old_tuple, e.get_tag());
    expr dec_proof_type = infer_type(dec_proof, cs);
    justification j = mk_type_mismatch_jst(dec_proof, dec_proof_type, expected_dec_proof_type, decreasing_proof(e));
    auto new_dec_proof_cs = ensure_has_type(dec_proof, dec_proof_type, expected_dec_proof_type, j);
    dec_proof = new_dec_proof_cs.first;
    cs       += new_dec_proof_cs.second;
    return mk_decreasing(dec_app, dec_proof);
}

bool elaborator::is_structure_like(expr const & S) {
    expr const & I = get_app_fn(S);
    return is_constant(I) && ::lean::is_structure_like(env(), const_name(I));
}

expr elaborator::visit_structure_instance(expr const & e, constraint_seq & cs) {
    expr S;
    buffer<name> field_names;
    buffer<expr> field_values, using_exprs;
    destruct_structure_instance(e, S, field_names, field_values, using_exprs);
    lean_assert(field_names.size() == field_values.size());
    expr new_S     = visit(S, cs);
    if (!is_structure_like(new_S))
        throw_elaborator_exception("invalid structure instance, given type is not a structure", S);
    buffer<expr> new_S_args;
    expr I = get_app_args(new_S, new_S_args);
    expr new_S_type = whnf(infer_type(new_S, cs), cs);
    tag S_tag = S.get_tag();
    while (is_pi(new_S_type)) {
        expr m     = m_full_context.mk_meta(m_ngen, some_expr(binding_domain(new_S_type)), S_tag);
        register_meta(m);
        new_S_args.push_back(m);
        new_S      = mk_app(new_S, m, S_tag);
        new_S_type = whnf(instantiate(binding_body(new_S_type), m), cs);
    }
    buffer<bool> field_used;
    field_used.resize(field_names.size(), false);
    buffer<expr> new_field_values;
    for (expr const & v : field_values)
        new_field_values.push_back(visit(v, cs));
    buffer<bool> using_exprs_used;
    using_exprs_used.resize(using_exprs.size(), false);
    buffer<expr> new_using_exprs;
    buffer<expr> new_using_types;
    for (expr const & u : using_exprs) {
        expr new_u = visit(u, cs);
        expr new_u_type = whnf(infer_type(new_u, cs), cs);
        if (!is_structure_like(new_u_type))
            throw_elaborator_exception("invalid structure instance, type of 'using' argument is not a structure", u);
        new_using_exprs.push_back(new_u);
        new_using_types.push_back(new_u_type);
    }
    buffer<name> intro_names;
    get_intro_rule_names(env(), const_name(I), intro_names);
    lean_assert(intro_names.size() == 1);
    name const & S_mk_name = intro_names[0];
    tag  result_tag = e.get_tag();
    expr S_mk = mk_constant(S_mk_name, const_levels(I), result_tag);
    for (expr & arg : new_S_args)
        S_mk  = mk_app(S_mk, arg, result_tag);
    expr S_mk_type = whnf(infer_type(S_mk, cs), cs);
    while (is_pi(S_mk_type)) {
        name n = binding_name(S_mk_type);
        expr d_type = binding_domain(S_mk_type);
        expr v;
        unsigned i = 0;
        for (; i < field_names.size(); i++) {
            if (!field_used[i] && field_names[i] == n) {
                field_used[i] = true;
                v = new_field_values[i];
                break;
            }
        }
        if (i == new_field_values.size()) {
            // did not find explicit field
            unsigned i = 0;
            for (; i < new_using_exprs.size(); i++) {
                // check if u_type structure has the given field.
                expr const & u_type = new_using_types[i];
                buffer<expr> u_type_args;
                expr const & J      = get_app_args(u_type, u_type_args);
                lean_assert(is_constant(J));
                name J_field_name = const_name(J) + n;
                if (env().find(J_field_name)) {
                    tag u_tag = using_exprs[i].get_tag();
                    v = mk_constant(J_field_name, const_levels(J), u_tag);
                    for (expr const & arg : u_type_args)
                        v = mk_app(v, arg, u_tag);
                    v = mk_app(v, new_using_exprs[i], u_tag);
                    using_exprs_used[i] = true;
                    break;
                }
            }
            if (i == using_exprs.size()) {
                // did not find field in using structure
                if (m_ctx.m_fail_missing_field) {
                    throw_elaborator_exception(sstream() << "invalid structure instance, field '"
                                               << n << "' is missing", e);
                }
                v = m_full_context.mk_meta(m_ngen, some_expr(d_type), result_tag);
                register_meta(v);
            }
        }
        S_mk            = mk_app(S_mk, v, result_tag);
        expr v_type     = infer_type(v, cs);
        justification j = mk_app_justification(S_mk, S_mk_type, v, v_type);
        auto new_v_cs   = ensure_has_type(v, v_type, d_type, j);
        expr new_v      = new_v_cs.first;
        cs             += new_v_cs.second;
        S_mk            = update_app(S_mk, app_fn(S_mk), new_v);
        S_mk_type = whnf(instantiate(binding_body(S_mk_type), new_v), cs);
    }
    for (unsigned i = 0; i < field_used.size(); i++) {
        if (!field_used[i])
            throw_elaborator_exception(sstream() << "invalid structure instance, invalid field name '"
                                       << field_names[i] << "'", field_values[i]);
    }
    for (unsigned i = 0; i < using_exprs_used.size(); i++) {
        if (!using_exprs_used[i])
            throw_elaborator_exception(sstream() << "invalid structure instance, 'using' clause #"
                                       << i + 1 << " is unnecessary", using_exprs[i]);
    }
    return S_mk;
}

expr elaborator::process_obtain_expr(list<obtain_struct> const & s_list, list<expr> const & from_list,
                                     expr const & goal, bool first, constraint_seq & cs, expr const & src) {
    lean_assert(length(s_list) == length(from_list));
    if (!s_list && !from_list)
        return visit(goal, cs);
    expr from       = head(from_list);
    obtain_struct s = head(s_list);
    lean_assert(!first || !s.is_leaf());
    if (s.is_leaf()) {
        lean_assert(is_local(from));
        expr const & from_type = mlocal_type(from);
        // fix user visible name
        expr d0          = binding_domain(goal);
        expr goal_domain = visit(d0, cs);
        if (is_placeholder(d0) && !is_explicit_placeholder(d0))
            save_binder_type(d0, goal_domain);
        expr new_from    = ::lean::mk_local(mlocal_name(from), binding_name(goal), goal_domain, binder_info());
        if (!is_lambda(goal))
            throw_elaborator_exception("invalid 'obtain' expression, insufficient number of local declarations", src);
        justification j = mk_type_mismatch_jst(new_from, goal_domain, from_type, src);
        if (!is_def_eq(from_type, goal_domain, j, cs))
            throw unifier_exception(j, substitution());
        flet<local_context> save1(m_context, m_context);
        flet<local_context> save2(m_full_context, m_full_context);
        m_context.add_local(new_from);
        m_full_context.add_local(new_from);
        expr new_goal   = instantiate(binding_body(goal), new_from);
        expr r = process_obtain_expr(tail(s_list), tail(from_list), new_goal, false, cs, src);
        return Fun(new_from, r);
    } else {
        lean_assert(!first || is_local(from));
        expr from_type  = whnf(infer_type(from, cs), cs);
        buffer<expr> I_args;
        expr I          = get_app_args(from_type, I_args);
        if (!is_constant(I)) {
            throw_elaborator_exception(src, [=](formatter const & fmt) {
                    format r = format("invalid 'obtain' expression, type of 'from' expression is not inductive");
                    r += pp_indent_expr(fmt, from_type);
                    return r;
                });
        }
        name const & I_name   = const_name(I);
        levels const & I_lvls = const_levels(I);
        if (!inductive::is_inductive_decl(env(), I_name))
            throw_elaborator_exception(sstream() << "invalid 'obtain' expression, '" << I_name
                                       << "' is not an inductive datatype", src);
        if (*inductive::get_num_intro_rules(env(), I_name) != 1)
            throw_elaborator_exception(sstream() << "invalid 'obtain' expression, '" << I_name
                                       << "' has more than one constructor", src);
        unsigned nparams      = *inductive::get_num_params(env(), I_name);
        unsigned nindices     = *inductive::get_num_indices(env(), I_name);
        declaration cases_on_decl = env().get({I_name, "cases_on"});
        levels cases_on_lvls = I_lvls;
        if (cases_on_decl.get_num_univ_params() != length(I_lvls))
            cases_on_lvls = cons(mk_meta_univ(m_ngen.next()), cases_on_lvls);
        expr cases_on = mk_constant(cases_on_decl.get_name(), cases_on_lvls);
        tag  g        = src.get_tag();
        expr R        = cases_on;
        for (unsigned i = 0; i < nparams; i++)
            R = mk_app(R, I_args[i], g);
        expr R_type   = whnf(infer_type(R, cs), cs);
        auto check_R_type = [&]() {
            if (!is_pi(R_type))
                throw_elaborator_exception(sstream() << "invalid 'obtain' expression, '"
                                           << I_name << "' has an ill-formed cases_on recursor", src);
        };
        check_R_type();
        expr motive_type = binding_domain(R_type);
        expr motive      = m_full_context.mk_meta(m_ngen, some_expr(motive_type), g);
        R                = mk_app(R, motive, g);
        R_type           = whnf(instantiate(binding_body(R_type), motive), cs);
        for (unsigned i = 0; i < nindices; i++) {
            check_R_type();
            expr index_type = binding_domain(R_type);
            expr index      = m_full_context.mk_meta(m_ngen, some_expr(index_type), g);
            R               = mk_app(R, index, g);
            R_type          = whnf(instantiate(binding_body(R_type), index), cs);
        }
        check_R_type();
        expr major_type = binding_domain(R_type);
        justification j = mk_type_mismatch_jst(from, from_type, major_type, src);
        if (!is_def_eq(from_type, major_type, j, cs))
            throw unifier_exception(j, substitution());
        R = mk_app(R, from, g);
        R_type = whnf(instantiate(binding_body(R_type), from), cs);
        check_R_type();
        expr minor_type = whnf(binding_domain(R_type), cs);
        buffer<expr> telescope;
        to_telescope(*m_tc, minor_type, telescope, optional<binder_info>(), cs);
        lean_assert(!s.is_leaf());
        buffer<obtain_struct> s_buffer;
        to_buffer(s.get_children(), s_buffer);
        if (telescope.size() == 0)
            throw_elaborator_exception(sstream() << "invalid 'obtain' expression, '" << I_name
                                       << "' is an empty type", src);
        if (s_buffer.size() < telescope.size())
            throw_elaborator_exception("invalid 'obtain' expression, insufficient number of local declarations", src);
        if (s_buffer.size() > telescope.size()) {
            obtain_struct s_tail(to_list(s_buffer.begin() + telescope.size() - 1, s_buffer.end()));
            s_buffer.shrink(telescope.size() - 1);
            s_buffer.push_back(s_tail);
        }
        lean_assert(s_buffer.size() == telescope.size());
        list<obtain_struct> new_s_list = to_list(s_buffer.begin(), s_buffer.end(), tail(s_list));
        list<expr> new_from_list       = to_list(telescope.begin(), telescope.end(), tail(from_list));
        expr minor = process_obtain_expr(new_s_list, new_from_list, goal, false, cs, src);
        expr infer_minor_type = infer_type(minor, cs);
        justification j2      = mk_type_mismatch_jst(minor, infer_minor_type, minor_type, src);
        if (!is_def_eq(infer_minor_type, minor_type, j2, cs))
            throw unifier_exception(j2, substitution());
        expr r    = mk_app(R, minor, g);
        if (!first)
            r = Fun(from, r);
        return r;
    }
}

expr elaborator::visit_obtain_expr(expr const & e, constraint_seq & cs) {
    lean_assert(is_obtain_expr(e));
    expr from, decls_goal;
    obtain_struct s;
    decompose_obtain(e, s, from, decls_goal);
    from       = visit(from, cs);
    return process_obtain_expr(to_list(s), to_list(from), decls_goal, true, cs, e);
}

expr elaborator::visit_core(expr const & e, constraint_seq & cs) {
    if (is_placeholder(e)) {
        return visit_placeholder(e, cs);
    } else if (is_choice(e)) {
        return visit_choice(e, none_expr(), cs);
    } else if (is_let_value(e)) {
        return visit_let_value(e, cs);
    } else if (is_by(e)) {
        return visit_by(e, none_expr(), cs);
    } else if (is_by_plus(e)) {
        return visit_by_plus(e, none_expr(), cs);
    } else if (is_calc_annotation(e)) {
        return visit_calc_proof(e, none_expr(), cs);
    } else if (is_no_info(e)) {
        flet<bool> let(m_no_info, true);
        return visit(get_annotation_arg(e), cs);
    } else if (is_typed_expr(e)) {
        return visit_typed_expr(e, cs);
    } else if (is_as_atomic(e)) {
        // ignore annotation
        return visit_core(get_as_atomic_arg(e), cs);
    } else if (is_consume_args(e)) {
        // ignore annotation
        return visit_core(get_consume_args_arg(e), cs);
    } else if (is_explicit(e)) {
        // ignore annotation
        return visit_core(get_explicit_arg(e), cs);
    } else if (is_sorry(e)) {
        return visit_sorry(e);
    } else if (is_equations(e)) {
        lean_unreachable();
    } else if (is_equation(e)) {
        return visit_equation(e, cs);
    } else if (is_inaccessible(e)) {
        return visit_inaccessible(e, cs);
    } else if (is_decreasing(e)) {
        return visit_decreasing(e, cs);
    } else if (is_structure_instance(e)) {
        return visit_structure_instance(e, cs);
    } else if (is_obtain_expr(e)) {
        return visit_obtain_expr(e, cs);
    } else {
        switch (e.kind()) {
        case expr_kind::Local:      return e;
        case expr_kind::Meta:       return e;
        case expr_kind::Sort:       return visit_sort(e);
        case expr_kind::Var:        lean_unreachable();  // LCOV_EXCL_LINE
        case expr_kind::Constant:   return visit_constant(e);
        case expr_kind::Macro:      return visit_macro(e, cs);
        case expr_kind::Lambda:     return visit_lambda(e, cs);
        case expr_kind::Pi:         return visit_pi(e, cs);
        case expr_kind::App:        return visit_app(e, cs);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }
}

pair<expr, constraint_seq> elaborator::visit(expr const & e) {
    if (is_extra_info(e)) {
        auto ecs = visit(get_annotation_arg(e));
        save_extra_type_data(e, ecs.first);
        return ecs;
    }
    if (is_notation_info(e)) {
        pair<expr, constraint_seq> ecs;
        {
            flet<bool> let(m_no_info, true);
            ecs = visit(get_annotation_arg(e));
        }
        save_type_data(e, ecs.first);
        return ecs;
    }
    expr r;
    expr b = e;
    constraint_seq cs;
    if (is_explicit(e)) {
        b    = get_explicit_arg(e);
        if (is_sorry(b)) {
            r = visit_constant(b);
        } else {
            r = visit_core(b, cs);
        }
    } else if (is_equations(e)) {
        r    = visit_equations(e, cs);
    } else if (is_explicit(get_app_fn(e))) {
        r    = visit_core(e, cs);
    } else {
        bool consume_args = false;
        if (is_as_atomic(e)) {
            flet<bool> let(m_no_info, true);
            r = get_as_atomic_arg(e);
            if (is_explicit(r)) r = get_explicit_arg(r);
            r = visit_core(r, cs);
        } else if (is_consume_args(e)) {
            consume_args = true;
            r = visit_core(get_consume_args_arg(e), cs);
        } else {
            r = visit_core(e, cs);
        }
        tag  g         = e.get_tag();
        expr r_type    = whnf(infer_type(r, cs), cs);
        expr imp_arg;
        bool is_strict = true;
        while (is_pi(r_type)) {
            binder_info bi = binding_info(r_type);
            if (!bi.is_implicit() && !bi.is_inst_implicit()) {
                if (!consume_args)
                    break;
                if (!has_free_var(binding_body(r_type), 0)) {
                    // if the rest of the type does not reference argument,
                    // then we also stop consuming arguments
                    break;
                }
            }
            bool inst_imp = bi.is_inst_implicit();
            imp_arg = mk_placeholder_meta(mk_mvar_suffix(r_type), some_expr(binding_domain(r_type)),
                                          g, is_strict, inst_imp, cs);
            r       = mk_app(r, imp_arg, g);
            r_type  = whnf(instantiate(binding_body(r_type), imp_arg), cs);
        }
    }
    save_type_data(b, r);
    return mk_pair(r, cs);
}

expr elaborator::visit(expr const & e, constraint_seq & cs) {
    auto r = visit(e);
    cs += r.second;
    return r.first;
}

unify_result_seq elaborator::solve(constraint_seq const & cs) {
    buffer<constraint> tmp;
    cs.linearize(tmp);
    return unify(env(), tmp.size(), tmp.data(), m_ngen.mk_child(), substitution(), m_unifier_config);
}

void elaborator::display_unsolved_proof_state(expr const & mvar, proof_state const & ps, char const * msg, expr const & pos) {
    lean_assert(is_metavar(mvar));
    if (!m_displayed_errors.contains(mlocal_name(mvar))) {
        m_displayed_errors.insert(mlocal_name(mvar));
        auto out = regular(env(), ios());
        flycheck_error err(out);
        display_error_pos(out, pip(), pos);
        out << " " << msg << "\n" << ps.pp(env(), ios()) << endl;
    }
}

void elaborator::display_unsolved_proof_state(expr const & mvar, proof_state const & ps, char const * msg) {
    display_unsolved_proof_state(mvar, ps, msg, mvar);
}

optional<expr> elaborator::get_pre_tactic_for(expr const & mvar) {
    if (auto it = m_local_tactic_hints.find(mlocal_name(mvar))) {
        m_used_local_tactic_hints.insert(mlocal_name(mvar));
        return some_expr(*it);
    } else {
        return none_expr();
    }
}

optional<tactic> elaborator::pre_tactic_to_tactic(expr const & pre_tac) {
    try {
        auto fn = [=](goal const & g, name_generator && ngen, expr const & e, optional<expr> const & expected_type,
                      substitution const & subst, bool report_unassigned) {
            elaborator aux_elaborator(m_ctx, std::move(ngen));
            // Disable tactic hints when processing expressions nested in tactics.
            // We must do it otherwise, it is easy to make the system loop.
            bool use_tactic_hints = false;
            return aux_elaborator.elaborate_nested(g.to_context(), expected_type, e,
                                                   use_tactic_hints, subst, report_unassigned);
        };
        return optional<tactic>(expr_to_tactic(env(), fn, pre_tac, pip()));
    } catch (expr_to_tactic_exception & ex) {
        auto out = regular(env(), ios());
        flycheck_error err(out);
        display_error_pos(out, pip(), ex.get_expr());
        out << " " << ex.what();
        out << pp_indent_expr(out.get_formatter(), pre_tac) << endl << "failed at:"
            << pp_indent_expr(out.get_formatter(), ex.get_expr()) << endl;
        return optional<tactic>();
    }
}

void elaborator::display_tactic_exception(tactic_exception const & ex, proof_state const & ps, expr const & pre_tac) {
    auto out = regular(env(), ios());
    flycheck_error err(out);
    if (optional<expr> const & e = ex.get_main_expr())
        display_error_pos(out, pip(), *e);
    else
        display_error_pos(out, pip(), pre_tac);
    out << ex.pp(out.get_formatter()) << "\nproof state:\n";
    if (auto curr_ps = ex.get_proof_state())
        out << curr_ps->pp(env(), ios()) << "\n";
    else
        out << ps.pp(env(), ios()) << "\n";
}

void elaborator::display_unsolved_subgoals(expr const & mvar, proof_state const & ps, expr const & pos) {
    unsigned ngoals = length(ps.get_goals());
    sstream s;
    s << ngoals << " unsolved subgoal";
    if (ngoals > 1) s << "s";
    display_unsolved_proof_state(mvar, ps, s.str().c_str(), pos);
}

void elaborator::display_unsolved_subgoals(expr const & mvar, proof_state const & ps) {
    display_unsolved_subgoals(mvar, ps, mvar);
}


/** \brief Try to instantiate meta-variable \c mvar (modulo its state ps) using the given tactic.
    If it succeeds, then update subst with the solution.
    Return true iff the metavariable \c mvar has been assigned.

    If \c show_failure == true, then display reason for failure.

    \remark the argument \c pre_tac is only used for error localization.
*/
bool elaborator::try_using(substitution & subst, expr const & mvar, proof_state const & ps,
                           expr const & pre_tac, tactic const & tac, bool show_failure) {
    lean_assert(length(ps.get_goals()) == 1);
    // make sure ps is a really a proof state for mvar.
    lean_assert(mlocal_name(get_app_fn(head(ps.get_goals()).get_meta())) == mlocal_name(mvar));
    try {
        proof_state_seq seq = tac(env(), ios(), ps);
        auto r = seq.pull();
        if (!r) {
            show_goal(ps, pre_tac, pre_tac, pre_tac);
            // tactic failed to produce any result
            if (show_failure)
                display_unsolved_proof_state(mvar, ps, "tactic failed");
            return false;
        } else if (!empty(r->first.get_goals())) {
            // tactic contains unsolved subgoals
            show_goal(r->first, pre_tac, pre_tac, pre_tac);
            if (show_failure)
                display_unsolved_subgoals(mvar, r->first);
            return false;
        } else {
            show_goal(ps, pre_tac, pre_tac, pre_tac);
            subst = r->first.get_subst();
            expr v = subst.instantiate(mvar);
            subst.assign(mlocal_name(mvar), v);
            return true;
        }
    } catch (tactic_exception & ex) {
        show_goal(ps, pre_tac, pre_tac, pre_tac);
        if (show_failure)
            display_tactic_exception(ex, ps, pre_tac);
        return false;
    }
}

static void extract_begin_end_tactics(expr pre_tac, buffer<expr> & pre_tac_seq) {
    if (is_begin_end_element_annotation(pre_tac)) {
        pre_tac_seq.push_back(get_annotation_arg(pre_tac));
    } else if (is_begin_end_annotation(pre_tac)) {
        // nested begin-end block
        pre_tac_seq.push_back(pre_tac);
    } else {
        buffer<expr> args;
        if (get_app_args(pre_tac, args) == get_and_then_tac_fn()) {
            for (expr const & arg : args) {
                extract_begin_end_tactics(arg, pre_tac_seq);
            }
        } else {
            throw exception("internal error, invalid begin-end tactic");
        }
    }
}

void elaborator::show_goal(proof_state const & ps, expr const & start, expr const & end, expr const & curr) {
    unsigned line, col;
    if (!m_ctx.has_show_goal_at(line, col))
        return;
    auto start_pos = pip()->get_pos_info(start);
    auto end_pos   = pip()->get_pos_info(end);
    auto curr_pos  = pip()->get_pos_info(curr);
    if (!start_pos || !end_pos || !curr_pos)
        return;
    if (start_pos->first > line || (start_pos->first == line && start_pos->second > col))
        return;
    if (end_pos->first < line || (end_pos->first == line && end_pos->second < col))
        return;
    if (curr_pos->first < line || (curr_pos->first == line && curr_pos->second < col))
        return;
    m_ctx.reset_show_goal_at();
    auto out = regular(env(), ios());
    print_lean_info_header(out.get_stream());
    out << "position " << curr_pos->first << ":" << curr_pos->second << "\n";
    out << ps.pp(env(), ios()) << "\n";
    print_lean_info_footer(out.get_stream());
}

bool elaborator::try_using_begin_end(substitution & subst, expr const & mvar, proof_state ps, expr const & pre_tac) {
    lean_assert(is_begin_end_annotation(pre_tac));
    expr end_expr   = pre_tac;
    expr start_expr = get_annotation_arg(pre_tac);
    buffer<expr> pre_tac_seq;
    extract_begin_end_tactics(get_annotation_arg(pre_tac), pre_tac_seq);
    for (expr ptac : pre_tac_seq) {
        if (is_begin_end_annotation(ptac)) {
            goals gs = ps.get_goals();
            if (!gs)
                throw_elaborator_exception("invalid nested begin-end block, there are no goals to be solved", ptac);
            goal  g             = head(gs);
            expr mvar           = g.get_mvar();
            name_generator ngen = ps.get_ngen();
            proof_state focus_ps(ps, goals(g), ngen.mk_child());
            if (!try_using_begin_end(subst, mvar, focus_ps, ptac))
                return false;
            ps = proof_state(ps, tail(gs), subst, ngen);
        } else {
            show_goal(ps, start_expr, end_expr, ptac);
            expr new_ptac = subst.instantiate_all(ptac);
            if (auto tac = pre_tactic_to_tactic(new_ptac)) {
                try {
                    ps = ps.update_report_failure(true);
                    proof_state_seq seq = (*tac)(env(), ios(), ps);
                    auto r = seq.pull();
                    if (!r) {
                        // tactic failed to produce any result
                        display_unsolved_proof_state(mvar, ps, "tactic failed", ptac);
                        return false;
                    }
                    if (m_ctx.m_flycheck_goals) {
                        if (auto p = pip()->get_pos_info(ptac)) {
                            auto out = regular(env(), ios());
                            flycheck_information info(out);
                            if (info.enabled()) {
                                display_information_pos(out, pip()->get_file_name(), p->first, p->second);
                                out << " proof state:\n" << ps.pp(env(), ios()) << "\n";
                            }
                        }
                    }
                    ps = r->first;
                } catch (tactic_exception & ex) {
                    display_tactic_exception(ex, ps, ptac);
                    return false;
                } catch (exception &) {
                    throw;
                } catch (throwable & ex) {
                    auto out = regular(env(), ios());
                    flycheck_error err(out);
                    display_error_pos(out, pip(), ptac);
                    out << ex.what() << "\nproof state:\n";
                    out << ps.pp(env(), ios()) << "\n";
                    return false;
                }
            } else {
                return false;
            }
        }
    }
    show_goal(ps, start_expr, end_expr, end_expr);

    if (!empty(ps.get_goals())) {
        display_unsolved_subgoals(mvar, ps, pre_tac);
        return false;
    } else {
        subst = ps.get_subst();
        lean_assert(subst.is_assigned(mvar));
        expr v = subst.instantiate(mvar);
        subst.assign(mlocal_name(mvar), v);
        return true;
    }
}

void elaborator::solve_unassigned_mvar(substitution & subst, expr mvar, name_set & visited) {
    if (visited.contains(mlocal_name(mvar)))
        return;
    visited.insert(mlocal_name(mvar));
    auto meta = mvar_to_meta(mvar);
    if (!meta)
        return;
    meta = instantiate_meta(*meta, subst);
    // TODO(Leo): we are discarding constraints here
    expr type = m_tc->infer(*meta).first;
    // first solve unassigned metavariables in type
    type = solve_unassigned_mvars(subst, type, visited);
    proof_state ps = to_proof_state(*meta, type, subst, m_ngen.mk_child());
    if (auto pre_tac = get_pre_tactic_for(mvar)) {
        if (is_begin_end_annotation(*pre_tac)) {
            try_using_begin_end(subst, mvar, ps, *pre_tac);
            return;
        }

        if (auto tac = pre_tactic_to_tactic(subst.instantiate_all(*pre_tac))) {
            bool show_failure = true;
            try_using(subst, mvar, ps, *pre_tac, *tac, show_failure);
            return;
        }
    }

    if (m_use_tactic_hints) {
        // using tactic_hints
        for (expr const & pre_tac : get_tactic_hints(env())) {
            if (auto tac = pre_tactic_to_tactic(pre_tac)) {
                bool show_failure = false;
                if (try_using(subst, mvar, ps, pre_tac, *tac, show_failure))
                    return;
            }
        }
    }
}

/** \brief Execute \c fn on every metavariable occurring in \c e.
    \remark The left-hand-side of equations is ignored.
*/
static void visit_unassigned_mvars(expr const & e, std::function<void(expr const &)> const & fn) {
    if (!has_metavar(e))
        return;

    expr_set visited;

    auto should_visit = [&](expr const & e) {
        if (!is_shared(e))
            return true;
        if (visited.find(e) != visited.end())
            return false;
        visited.insert(e);
        return true;
    };

    std::function<void(expr const & e)> visit = [&](expr const & e) {
        check_interrupted();
        if (!has_metavar(e))
            return;
        switch (e.kind()) {
        case expr_kind::Var:      case expr_kind::Local:
        case expr_kind::Constant: case expr_kind::Sort:
            break; // do nothing
        case expr_kind::Meta:
            if (should_visit(e))
                fn(e);
            break;
        case expr_kind::Macro:
            if (should_visit(e)) {
                if (is_equation(e)) {
                    visit(equation_rhs(e));
                } else {
                    for (unsigned i = 0; i < macro_num_args(e); i++)
                        visit(macro_arg(e, i));
                }
            }
            break;
        case expr_kind::App:
            if (should_visit(e)) {
                visit(app_fn(e));
                visit(app_arg(e));
            }
            break;
        case expr_kind::Lambda:
        case expr_kind::Pi:
            if (should_visit(e)) {
                visit(binding_domain(e));
                visit(binding_body(e));
            }
            break;
        }
    };

    visit(e);
}

expr elaborator::solve_unassigned_mvars(substitution & subst, expr e, name_set & visited) {
    e = subst.instantiate(e);
    visit_unassigned_mvars(e, [&](expr const & mvar) {
            solve_unassigned_mvar(subst, mvar, visited);
        });
    return subst.instantiate(e);
}

expr elaborator::solve_unassigned_mvars(substitution & subst, expr const & e) {
    name_set visited;
    return solve_unassigned_mvars(subst, e, visited);
}

bool elaborator::display_unassigned_mvars(expr const & e, substitution const & s) {
    bool r = false;
    if (check_unassigned() && has_metavar(e)) {
        substitution tmp_s(s);
        visit_unassigned_mvars(e, [&](expr const & mvar) {
                if (auto it = mvar_to_meta(mvar)) {
                    expr meta      = tmp_s.instantiate(*it);
                    expr meta_type = tmp_s.instantiate(type_checker(env()).infer(meta).first);
                    goal g(meta, meta_type);
                    proof_state ps(goals(g), s, m_ngen, constraints());
                    display_unsolved_proof_state(mvar, ps, "don't know how to synthesize placeholder");
                    r = true;
                }
            });
    }
    return r;
}

/** \brief Check whether the solution found by the elaborator is producing too specific
    universes.

    \remark For now, we only check if a term Type.{?u} was solved by assigning ?u to 0.
    In this case, the user should write Prop instead of Type.
*/
void elaborator::check_sort_assignments(substitution const & s) {
    for (auto const & p : m_to_check_sorts) {
        expr pre  = p.first;
        expr post = p.second;
        lean_assert(is_sort(post));
        for_each(sort_level(post), [&](level const & u) {
                if (is_meta(u) && s.is_assigned(u)) {
                    level r = *s.get_level(u);
                    if (is_explicit(r)) {
                        substitution saved_s(s);
                        throw_kernel_exception(env(), pre, [=](formatter const & fmt) {
                                options o = fmt.get_options();
                                o  = o.update(get_pp_universes_option_name(), true);
                                format r("solution computed by the elaborator forces a universe placeholder"
                                         " to be a fixed value, computed sort is");
                                r += pp_indent_expr(fmt.update_options(o), substitution(saved_s).instantiate(post));
                                return r;
                            });
                    }
                }
                return true;
            });
    }
}

/** \brief Apply substitution and solve remaining metavariables using tactics. */
expr elaborator::apply(substitution & s, expr const & e, name_set & univ_params, buffer<name> & new_params) {
    expr r = s.instantiate(e);
    if (has_univ_metavar(r))
        r = univ_metavars_to_params(env(), lls(), s, univ_params, new_params, r);
    r = solve_unassigned_mvars(s, r);
    display_unassigned_mvars(r, s);
    return r;
}

std::tuple<expr, level_param_names> elaborator::apply(substitution & s, expr const & e) {
    auto ps = collect_univ_params(e);
    buffer<name> new_ps;
    expr r = apply(s, e, ps, new_ps);
    return std::make_tuple(r, to_list(new_ps.begin(), new_ps.end()));
}

struct pos_info_hash {
    unsigned operator()(pos_info const & p) const { return hash(p.first, p.second); }
};

void elaborator::check_used_local_tactic_hints() {
    std::unordered_set<pos_info, pos_info_hash, std::equal_to<pos_info>> pos_set;
    // The same pretac may be processed several times because of choice-exprs.
    // The pretactics may be structurally different in each branch (because of unique local constant names).
    // So, we use their positions to identify which tactic hints were used
    if (!pip())
        return; // position information is not available
    m_local_tactic_hints.for_each([&](name const & n, expr const & e) {
            if (m_used_local_tactic_hints.contains(n)) {
                if (auto p = pip()->get_pos_info(e)) {
                    pos_set.insert(*p);
                }
            }
        });
    m_local_tactic_hints.for_each([&](name const & n, expr const & e) {
            if (m_used_local_tactic_hints.contains(n))
                return; // local hint was used
            if (auto p = pip()->get_pos_info(e)) {
                if (pos_set.find(*p) == pos_set.end()) {
                    char const * msg = "unnecessary tactic was provided, placeholder was automatically "
                        "synthesized by the elaborator";
                    if (auto it = m_mvar2meta.find(n))
                        throw_elaborator_exception(msg, *it);
                    else
                        throw exception(msg);
                }
            }
            // Remark: we are ignoring expressions that do not have location information.
            // This is a little bit hackish
        });
}

auto elaborator::operator()(list<expr> const & ctx, expr const & e, bool _ensure_type)
-> std::tuple<expr, level_param_names> {
    m_context.set_ctx(ctx);
    m_full_context.set_ctx(ctx);
    constraint_seq cs;
    expr r = visit(e, cs);
    if (_ensure_type)
        r = ensure_type(r, cs);
    auto p  = solve(cs).pull();
    lean_assert(p);
    substitution s = p->first.first;
    auto result = apply(s, r);
    check_sort_assignments(s);
    instantiate_info(s);
    check_used_local_tactic_hints();
    return result;
}

std::tuple<expr, expr, level_param_names> elaborator::operator()(expr const & t, expr const & v, name const & n) {
    constraint_seq t_cs;
    expr r_t      = ensure_type(visit(t, t_cs), t_cs);
    // Opaque definitions in the main module may treat other opaque definitions (in the main module) as transparent.
    constraint_seq v_cs;
    expr r_v      = visit(v, v_cs);
    expr r_v_type = infer_type(r_v, v_cs);
    justification j = mk_justification(r_v, [=](formatter const & fmt, substitution const & subst, bool as_error) {
            substitution s(subst);
            return pp_def_type_mismatch(fmt, n, s.instantiate(r_t), s.instantiate(r_v_type), as_error);
        });
    pair<expr, constraint_seq> r_v_cs = ensure_has_type(r_v, r_v_type, r_t, j);
    r_v = r_v_cs.first;
    constraint_seq cs = t_cs + r_v_cs.second + v_cs;
    auto p  = solve(cs).pull();
    lean_assert(p);
    substitution s = p->first.first;
    name_set univ_params = collect_univ_params(r_v, collect_univ_params(r_t));
    buffer<name> new_params;
    expr new_r_t = apply(s, r_t, univ_params, new_params);
    expr new_r_v = apply(s, r_v, univ_params, new_params);
    check_sort_assignments(s);
    instantiate_info(s);
    check_used_local_tactic_hints();
    return std::make_tuple(new_r_t, new_r_v, to_list(new_params.begin(), new_params.end()));
}

// Auxiliary procedure for #translate
static expr translate_local_name(environment const & env,
                                 list<expr> const & ctx, name const & local_name,
                                 expr const & src) {
    for (expr const & local : ctx) {
        if (local_pp_name(local) == local_name)
            return copy(local);
    }
    if (env.find(local_name)) {
        if (is_local(src))
            return mk_constant(local_name);
        else
            return src;
    }
    throw_elaborator_exception(sstream() << "unknown identifier '" << local_name << "'", src);
}

/** \brief Translated local constants (and undefined constants) occurring in \c e into
    local constants provided by \c ctx.
    Throw exception is \c ctx does not contain the local constant.
*/
static expr translate(environment const & env, list<expr> const & ctx, expr const & e) {
    auto fn = [&](expr const & e) {
        if (is_placeholder(e) || is_by(e)) {
            return some_expr(e); // ignore placeholders
        } else if (is_constant(e)) {
            expr new_e = copy_tag(e, translate_local_name(env, ctx, const_name(e), e));
            return some_expr(new_e);
        } else if (is_local(e)) {
            expr new_e = copy_tag(e, translate_local_name(env, ctx, local_pp_name(e), e));
            return some_expr(new_e);
        } else {
            return none_expr();
        }
    };
    return replace(e, fn);
}

/** \brief Elaborate expression \c e in context \c ctx. */
elaborate_result elaborator::elaborate_nested(list<expr> const & ctx, optional<expr> const & expected_type,
                                              expr const & n, bool use_tactic_hints,
                                              substitution const & subst, bool report_unassigned) {
    if (infom()) {
        if (auto ps = get_info_tactic_proof_state()) {
            save_proof_state_info(*ps, n);
        }
    }
    expr e = translate(env(), ctx, n);
    metavar_closure cls;
    if (expected_type) {
        e = copy_tag(e, mk_typed_expr(mk_as_is(*expected_type), e));
        cls.add(*expected_type);
    }
    m_context.set_ctx(ctx);
    m_context.set_ctx(ctx);
    m_full_context.set_ctx(ctx);
    flet<bool> set_discard(m_unifier_config.m_discard, false);
    flet<bool> set_use_hints(m_use_tactic_hints, use_tactic_hints);
    constraint_seq cs;
    expr r  = visit(e, cs);

    buffer<constraint> tmp;
    cs.linearize(tmp);
    auto p  = unify(env(), tmp.size(), tmp.data(), m_ngen.mk_child(), subst, m_unifier_config).pull();
    lean_assert(p);
    substitution new_subst = p->first.first;
    constraints rcs        = p->first.second;
    r = new_subst.instantiate_all(r);
    r = solve_unassigned_mvars(new_subst, r);
    rcs = map(rcs, [&](constraint const & c) { return instantiate_metavars(c, new_subst); });
    instantiate_info(new_subst);
    if (report_unassigned)
        display_unassigned_mvars(r, new_subst);
    if (expected_type) {
        justification j;
        rcs = append(rcs, cls.mk_constraints(new_subst, j));
    }
    return elaborate_result(r, new_subst, rcs);
}

static name * g_tmp_prefix = nullptr;

std::tuple<expr, level_param_names> elaborate(elaborator_context & env, list<expr> const & ctx, expr const & e,
                                              bool ensure_type, bool nice_mvar_names) {
    return elaborator(env, name_generator(*g_tmp_prefix), nice_mvar_names)(ctx, e, ensure_type);
}

std::tuple<expr, expr, level_param_names> elaborate(elaborator_context & env, name const & n, expr const & t,
                                                    expr const & v) {
    return elaborator(env, name_generator(*g_tmp_prefix))(t, v, n);
}

void initialize_elaborator() {
    g_tmp_prefix = new name(name::mk_internal_unique_name());
}

void finalize_elaborator() {
    delete g_tmp_prefix;
}
}
