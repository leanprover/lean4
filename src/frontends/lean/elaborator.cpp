/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include "util/flet.h"
#include "util/list_fn.h"
#include "util/lazy_list_fn.h"
#include "util/sstream.h"
#include "util/name_map.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/kernel_exception.h"
#include "kernel/error_msgs.h"
#include "kernel/expr_maps.h"
#include "library/coercion.h"
#include "library/placeholder.h"
#include "library/choice.h"
#include "library/explicit.h"
#include "library/unifier.h"
#include "library/opaque_hints.h"
#include "library/locals.h"
#include "library/let.h"
#include "library/deep_copy.h"
#include "library/metavar_closure.h"
#include "library/typed_expr.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/error_handling/error_handling.h"
#include "frontends/lean/local_decls.h"
#include "frontends/lean/class.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tactic_hint.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/no_info.h"
#include "frontends/lean/extra_info.h"
#include "frontends/lean/local_context.h"
#include "frontends/lean/choice_iterator.h"
#include "frontends/lean/placeholder_elaborator.h"
#include "frontends/lean/coercion_elaborator.h"

#ifndef LEAN_DEFAULT_ELABORATOR_LOCAL_INSTANCES
#define LEAN_DEFAULT_ELABORATOR_LOCAL_INSTANCES true
#endif

namespace lean {
// ==========================================
// elaborator configuration options
static name g_elaborator_local_instances{"elaborator", "local_instances"};
RegisterBoolOption(g_elaborator_local_instances, LEAN_DEFAULT_ELABORATOR_LOCAL_INSTANCES, "(lean elaborator) use local declarates as class instances");
bool get_elaborator_local_instances(options const & opts) {
    return opts.get_bool(g_elaborator_local_instances, LEAN_DEFAULT_ELABORATOR_LOCAL_INSTANCES);
}
// ==========================================

elaborator_context::elaborator_context(environment const & env, io_state const & ios, local_decls<level> const & lls,
                                       pos_info_provider const * pp, info_manager * info, bool check_unassigned):
    m_env(env), m_ios(ios), m_lls(lls), m_pos_provider(pp), m_info_manager(info), m_check_unassigned(check_unassigned) {
    m_use_local_instances = get_elaborator_local_instances(ios.get_options());
}

/** \brief Helper class for implementing the \c elaborate functions. */
class elaborator : public coercion_info_manager {
    typedef name_map<expr> local_tactic_hints;
    typedef rb_map<expr, pair<expr, constraint_seq>, expr_quick_cmp> cache;

    elaborator_context & m_env;
    name_generator       m_ngen;
    type_checker_ptr     m_tc[2];
    // mapping from metavariable ?m to the (?m l_1 ... l_n) where [l_1 ... l_n] are the local constants
    // representing the context where ?m was created.
    local_context        m_context; // current local context: a list of local constants
    local_context        m_full_context; // superset of m_context, it also contains non-contextual locals.
    cache                m_cache;

    // mapping from metavariable name ?m to tactic expression that should be used to solve it.
    // this mapping is populated by the 'by tactic-expr' expression.
    local_tactic_hints   m_local_tactic_hints;
    // set of metavariables that we already reported unsolved/unassigned
    name_set             m_displayed_errors;
    // if m_relax_main_opaque is true, then treat opaque definitions from the main module as transparent.
    bool                 m_relax_main_opaque;
    // if m_no_info is true, we do not collect information when true,
    // we set is to true whenever we find no_info annotation.
    bool                 m_no_info;
    info_manager         m_pre_info_data;
    unifier_config       m_unifier_config;

    // Auxiliary object to "saving" elaborator state
    struct saved_state {
        list<expr> m_ctx;
        list<expr> m_full_ctx;
        cache      m_cache;
        saved_state(elaborator & e):
            m_ctx(e.m_context.get_data()), m_full_ctx(e.m_full_context.get_data()), m_cache(e.m_cache) {}
    };

    struct scope_ctx {
        elaborator &         m_main;
        local_context::scope m_scope1;
        local_context::scope m_scope2;
        cache                m_old_cache;
        scope_ctx(elaborator & e):m_main(e), m_scope1(e.m_context), m_scope2(e.m_full_context), m_old_cache(e.m_cache) {}
        ~scope_ctx() { m_main.m_cache = m_old_cache; }
    };

    /** \brief Auxiliary object for creating backtracking points, and replacing the local scopes. */
    struct new_scope {
        elaborator &                 m_main;
        bool                         m_old_no_info;
        local_context::scope_replace m_context_scope;
        local_context::scope_replace m_full_context_scope;
        cache                        m_old_cache;
        new_scope(elaborator & e, saved_state const & s, bool no_info = false):
            m_main(e),
            m_context_scope(e.m_context, s.m_ctx),
            m_full_context_scope(e.m_full_context, s.m_full_ctx){
            m_old_no_info    = m_main.m_no_info;
            m_main.m_no_info = no_info;
            m_old_cache     = m_main.m_cache;
            m_main.m_cache  = s.m_cache;
        }
        ~new_scope() {
            m_main.m_no_info = m_old_no_info;
            m_main.m_cache  = m_old_cache;
        }
    };

    /** \brief 'Choice' expressions <tt>(choice e_1 ... e_n)</tt> are mapped into a metavariable \c ?m
        and a choice constraints <tt>(?m in fn)</tt> where \c fn is a choice function.
        The choice function produces a stream of alternatives. In this case, it produces a stream of
        size \c n, one alternative for each \c e_i.
        This is a helper class for implementing this choice functions.
    */
    struct choice_expr_elaborator : public choice_iterator {
        elaborator & m_elab;
        expr         m_mvar;
        expr         m_choice;
        saved_state  m_state;
        unsigned     m_idx;
        bool         m_relax_main_opaque;
        choice_expr_elaborator(elaborator & elab, expr const & mvar, expr const & c,
                               saved_state const & s, bool relax):
            m_elab(elab), m_mvar(mvar), m_choice(c), m_state(s),
            m_idx(get_num_choices(m_choice)), m_relax_main_opaque(relax) {
        }

        virtual optional<constraints> next() {
            while (m_idx > 0) {
                --m_idx;
                expr const & c = get_choice(m_choice, m_idx);
                expr const & f = get_app_fn(c);
                m_elab.save_identifier_info(f);
                try {
                    new_scope s(m_elab, m_state);
                    pair<expr, constraint_seq> rcs = m_elab.visit(c);
                    expr r = rcs.first;
                    constraint_seq cs = mk_eq_cnstr(m_mvar, r, justification(), m_relax_main_opaque) + rcs.second;
                    return optional<constraints>(cs.to_list());
                } catch (exception &) {}
            }
            return optional<constraints>();
        }
    };

public:
    elaborator(elaborator_context & env, list<expr> const & ctx, name_generator const & ngen):
        m_env(env),
        m_ngen(ngen),
        m_context(m_ngen.next(), ctx),
        m_full_context(m_ngen.next(), ctx),
        m_unifier_config(env.m_ios.get_options(), true /* use exceptions */, true /* discard */) {
        m_relax_main_opaque = false;
        m_no_info = false;
        m_tc[0]  = mk_type_checker_with_hints(env.m_env, m_ngen.mk_child(), false);
        m_tc[1]  = mk_type_checker_with_hints(env.m_env, m_ngen.mk_child(), true);
    }

    environment const & env() const { return m_env.m_env; }
    io_state const & ios() const { return m_env.m_ios; }
    local_decls<level> const & lls() const { return m_env.m_lls; }
    bool use_local_instances() const { return m_env.m_use_local_instances; }
    info_manager * infom() const { return m_env.m_info_manager; }
    pos_info_provider const * pip() const { return m_env.m_pos_provider; }
    bool check_unassigned() const { return m_env.m_check_unassigned; }

    expr mk_local(name const & n, expr const & t, binder_info const & bi) {
        return ::lean::mk_local(m_ngen.next(), n, t, bi);
    }

    pair<expr, constraint_seq> infer_type(expr const & e) { return m_tc[m_relax_main_opaque]->infer(e); }
    pair<expr, constraint_seq> whnf(expr const & e) { return m_tc[m_relax_main_opaque]->whnf(e); }
    expr infer_type(expr const & e, constraint_seq & s) { return m_tc[m_relax_main_opaque]->infer(e, s); }
    expr whnf(expr const & e, constraint_seq & s) { return m_tc[m_relax_main_opaque]->whnf(e, s); }
    expr mk_app(expr const & f, expr const & a, tag g) { return ::lean::mk_app(f, a).set_tag(g); }

    /** \brief Convert the metavariable to the metavariable application that captures
        the context where it was defined.
    */
    optional<expr> mvar_to_meta(expr const & mvar) {
        lean_assert(is_metavar(mvar));
        name const & m = mlocal_name(mvar);
        if (auto it = m_context.find_meta(m))
            return it;
        else
            return m_full_context.find_meta(m);
    }

    /** \brief Store the pair (pos(e), type(r)) in the info_data if m_info_manager is available. */
    void save_type_data(expr const & e, expr const & r) {
        if (!m_no_info && infom() && pip() && (is_constant(e) || is_local(e) || is_placeholder(e))) {
            if (auto p = pip()->get_pos_info(e)) {
                expr t = m_tc[m_relax_main_opaque]->infer(r).first;
                m_pre_info_data.add_type_info(p->first, p->second, t);
            }
        }
    }

    /** \brief Store type information at pos(e) for r if \c e is marked as "extra" in the info_manager */
    void save_extra_type_data(expr const & e, expr const & r) {
        if (!m_no_info && infom() && pip()) {
            if (auto p = pip()->get_pos_info(e)) {
                expr t = m_tc[m_relax_main_opaque]->infer(r).first;
                m_pre_info_data.add_extra_type_info(p->first, p->second, r, t);
            }
        }
    }

    /** \brief Auxiliary function for saving information about which overloaded identifier was used by the elaborator. */
    void save_identifier_info(expr const & f) {
        if (!m_no_info && infom() && pip() && is_constant(f)) {
            if (auto p = pip()->get_pos_info(f))
                m_pre_info_data.add_identifier_info(p->first, p->second, const_name(f));
        }
    }

    /** \brief Store actual term that was synthesized for an explicit placeholders */
    void save_synth_data(expr const & e, expr const & r) {
        if (!m_no_info && infom() && pip() && is_placeholder(e)) {
            if (auto p = pip()->get_pos_info(e))
                m_pre_info_data.add_synth_info(p->first, p->second, r);
        }
    }

    void save_placeholder_info(expr const & e, expr const & r) {
        if (is_explicit_placeholder(e)) {
            save_type_data(e, r);
            save_synth_data(e, r);
        }
    }

    /** \brief Auxiliary function for saving information about which coercion was used by the elaborator.
        It marks that coercion c was used on e.
    */
    virtual void save_coercion_info(expr const & e, expr const & c) {
        if (!m_no_info && infom() && pip()) {
            if (auto p = pip()->get_pos_info(e)) {
                expr t = m_tc[m_relax_main_opaque]->infer(c).first;
                m_pre_info_data.add_coercion_info(p->first, p->second, c, t);
            }
        }
    }

    /** \brief Remove coercion information associated with \c e */
    virtual void erase_coercion_info(expr const & e) {
        if (!m_no_info && infom() && pip()) {
            if (auto p = pip()->get_pos_info(e))
                m_pre_info_data.erase_coercion_info(p->first, p->second);
        }
    }

    void copy_info_to_manager(substitution s) {
        if (!infom())
            return;
        m_pre_info_data.instantiate(s);
        bool overwrite = true;
        infom()->merge(m_pre_info_data, overwrite);
        m_pre_info_data.clear();
    }

    /** \brief Create a metavariable, and attach choice constraint for generating
        solutions using class-instances and tactic-hints.
    */
    expr mk_placeholder_meta(optional<expr> const & type, tag g, bool is_strict, constraint_seq & cs) {
        auto ec = mk_placeholder_elaborator(env(), ios(), m_context.get_data(),
                                            m_ngen.next(), m_relax_main_opaque, use_local_instances(),
                                            is_strict, type, g);
        cs += ec.second;
        return ec.first;
    }

    expr visit_expecting_type(expr const & e, constraint_seq & cs) {
        if (is_placeholder(e) && !placeholder_type(e)) {
            expr r = m_context.mk_type_meta(e.get_tag());
            save_placeholder_info(e, r);
            return r;
        } else {
            return visit(e, cs);
        }
    }

    expr visit_expecting_type_of(expr const & e, expr const & t, constraint_seq & cs) {
        if (is_placeholder(e) && !placeholder_type(e)) {
            expr r = mk_placeholder_meta(some_expr(t), e.get_tag(), is_strict_placeholder(e), cs);
            save_placeholder_info(e, r);
            return r;
        } else if (is_choice(e)) {
            return visit_choice(e, some_expr(t), cs);
        } else if (is_by(e)) {
            return visit_by(e, some_expr(t), cs);
        } else {
            return visit(e, cs);
        }
    }

    expr visit_choice(expr const & e, optional<expr> const & t, constraint_seq & cs) {
        lean_assert(is_choice(e));
        // Possible optimization: try to lookahead and discard some of the alternatives.
        expr m              = m_full_context.mk_meta(t, e.get_tag());
        saved_state s(*this);
        bool relax          = m_relax_main_opaque;
        auto fn = [=](expr const & mvar, expr const & /* type */, substitution const & /* s */,
                      name_generator const & /* ngen */) {
            return choose(std::make_shared<choice_expr_elaborator>(*this, mvar, e, s, relax));
        };
        justification j = mk_justification("none of the overloads is applicable", some_expr(e));
        cs += mk_choice_cnstr(m, fn, to_delay_factor(cnstr_group::Basic), true, j, m_relax_main_opaque);
        return m;
    }

    expr visit_by(expr const & e, optional<expr> const & t, constraint_seq & cs) {
        lean_assert(is_by(e));
        expr tac = visit(get_by_arg(e), cs);
        expr m   = m_context.mk_meta(t, e.get_tag());
        m_local_tactic_hints.insert(mlocal_name(get_app_fn(m)), tac);
        return m;
    }

    /** \brief Make sure \c f is really a function, if it is not, try to apply coercions.
        The result is a pair <tt>new_f, f_type</tt>, where new_f is the new value for \c f,
        and \c f_type is its type (and a Pi-expression)
    */
    pair<expr, expr> ensure_fun(expr f, constraint_seq & cs) {
        expr f_type = infer_type(f, cs);
        if (!is_pi(f_type))
            f_type = whnf(f_type, cs);
        if (!is_pi(f_type) && has_metavar(f_type)) {
            constraint_seq saved_cs = cs;
            expr new_f_type = whnf(f_type, cs);
            if (!is_pi(new_f_type) && is_meta(new_f_type)) {
                cs = saved_cs;
                // let type checker add constraint
                f_type = m_tc[m_relax_main_opaque]->ensure_pi(f_type, f, cs);
            } else {
                f_type = new_f_type;
            }
        }
        if (!is_pi(f_type)) {
            // try coercion to function-class
            optional<expr> c = get_coercion_to_fun(env(), f_type);
            if (c) {
                expr old_f = f;
                f = mk_app(*c, f, f.get_tag());
                f_type = infer_type(f, cs);
                save_coercion_info(old_f, f);
                lean_assert(is_pi(f_type));
            } else {
                throw_kernel_exception(env(), f, [=](formatter const & fmt) { return pp_function_expected(fmt, f); });
            }
        } else {
            erase_coercion_info(f);
        }
        lean_assert(is_pi(f_type));
        return mk_pair(f, f_type);
    }

    bool has_coercions_from(expr const & a_type) {
        expr const & a_cls = get_app_fn(whnf(a_type).first);
        return is_constant(a_cls) && ::lean::has_coercions_from(env(), const_name(a_cls));
    }

    bool has_coercions_to(expr const & d_type) {
        expr const & d_cls = get_app_fn(whnf(d_type).first);
        return is_constant(d_cls) && ::lean::has_coercions_to(env(), const_name(d_cls));
    }

    expr apply_coercion(expr const & a, expr a_type, expr d_type) {
        a_type = whnf(a_type).first;
        d_type = whnf(d_type).first;
        expr const & d_cls = get_app_fn(d_type);
        if (is_constant(d_cls)) {
            if (auto c = get_coercion(env(), a_type, const_name(d_cls))) {
                expr r = mk_app(*c, a, a.get_tag());
                save_coercion_info(a, r);
                return r;
            } else {
                erase_coercion_info(a);
            }
        }
        return a;
    }

    /** \brief Given a term <tt>a : a_type</tt>, and an expected type generate a metavariable with a delayed coercion. */
    pair<expr, constraint_seq> mk_delayed_coercion(expr const & a, expr const & a_type, expr const & expected_type,
                                                   justification const & j) {
        bool relax = m_relax_main_opaque;
        type_checker & tc = *m_tc[relax];
        pair<expr, constraint> ec = mk_coercion_elaborator(tc, *this, m_full_context, relax,
                                                           a, a_type, expected_type, j);
        return to_ecs(ec.first, ec.second);
    }

    /** \brief Given a term <tt>a : a_type</tt>, ensure it has type \c expected_type. Apply coercions if needed

        \remark relax == true affects how opaque definitions in the main module are treated.
    */
    pair<expr, constraint_seq> ensure_has_type(expr const & a, expr const & a_type, expr const & expected_type,
                                               justification const & j, bool relax) {
        if (is_meta(expected_type) && has_coercions_from(a_type)) {
            return mk_delayed_coercion(a, a_type, expected_type, j);
        } else if (is_meta(a_type) && has_coercions_to(expected_type)) {
            return mk_delayed_coercion(a, a_type, expected_type, j);
        } else {
            auto dcs = m_tc[relax]->is_def_eq(a_type, expected_type, j);
            if (dcs.first) {
                return to_ecs(a, dcs.second);
            } else {
                expr new_a = apply_coercion(a, a_type, expected_type);
                bool coercion_worked = false;
                constraint_seq cs;
                if (!is_eqp(a, new_a)) {
                    expr new_a_type = infer_type(new_a, cs);
                    coercion_worked = m_tc[relax]->is_def_eq(new_a_type, expected_type, j, cs);
                }
                if (coercion_worked) {
                    return to_ecs(new_a, cs);
                } else if (has_metavar(a_type) || has_metavar(expected_type)) {
                    // rely on unification hints to solve this constraint
                    return to_ecs(a, mk_eq_cnstr(a_type, expected_type, j, relax));
                } else {
                    throw unifier_exception(j, substitution());
                }
            }
        }
    }

    bool is_choice_app(expr const & e) {
        expr const & f = get_app_fn(e);
        return is_choice(f) || (is_annotation(f) && is_choice(get_nested_annotation_arg(f)));
    }

    /** \brief Process ((choice f_1 ... f_n) a_1 ... a_k) as
        (choice (f_1 a_1 ... a_k) ... (f_n a_1 ... a_k))
    */
    expr visit_choice_app(expr const & e, constraint_seq & cs) {
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

    expr visit_app(expr const & e, constraint_seq & cs) {
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
            while (binding_info(f_type).is_strict_implicit() || (!first && binding_info(f_type).is_implicit())) {
                tag g          = f.get_tag();
                bool is_strict = false;
                expr imp_arg   = mk_placeholder_meta(some_expr(binding_domain(f_type)), g, is_strict, f_cs);
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
        expr a      = visit_expecting_type_of(app_arg(e), d_type, a_cs);
        expr a_type = infer_type(a, a_cs);
        expr r      = mk_app(f, a, e.get_tag());

        justification j = mk_app_justification(r, a, d_type, a_type);
        auto new_a_cs   = ensure_has_type(a, a_type, d_type, j, m_relax_main_opaque);
        expr new_a      = new_a_cs.first;
        cs += f_cs + new_a_cs.second + a_cs;
        return update_app(r, app_fn(r), new_a);
    }

    expr visit_placeholder(expr const & e, constraint_seq & cs) {
        expr r = mk_placeholder_meta(placeholder_type(e), e.get_tag(), is_strict_placeholder(e), cs);
        save_placeholder_info(e, r);
        return r;
    }

    level replace_univ_placeholder(level const & l) {
        return replace(l, [&](level const & l) {
                if (is_placeholder(l))
                    return some_level(mk_meta_univ(m_ngen.next()));
                else
                    return none_level();
            });
    }

    expr visit_sort(expr const & e) {
        return update_sort(e, replace_univ_placeholder(sort_level(e)));
    }

    expr visit_macro(expr const & e, constraint_seq & cs) {
        if (is_as_is(e)) {
            return get_as_is_arg(e);
        } else {
            // Remark: Macros are not meant to be used in the front end.
            // Perhaps, we should throw error.
            buffer<expr> args;
            for (unsigned i = 0; i < macro_num_args(e); i++)
                args.push_back(visit(macro_arg(e, i), cs));
            return update_macro(e, args.size(), args.data());
        }
    }

    expr visit_constant(expr const & e) {
        declaration d = env().get(const_name(e));
        buffer<level> ls;
        for (level const & l : const_levels(e))
            ls.push_back(replace_univ_placeholder(l));
        unsigned num_univ_params = length(d.get_univ_params());
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
    expr ensure_type(expr const & e, constraint_seq & cs) {
        expr t = infer_type(e, cs);
        erase_coercion_info(e);
        if (is_sort(t))
            return e;
        t = whnf(t, cs);
        if (is_sort(t))
            return e;
        if (has_metavar(t)) {
            t = whnf(t, cs);
            if (is_sort(t))
                return e;
            if (is_meta(t)) {
                // let type checker add constraint
                m_tc[m_relax_main_opaque]->ensure_sort(t, e, cs);
                return e;
            }
        }
        optional<expr> c = get_coercion_to_sort(env(), t);
        if (c) {
            expr r = mk_app(*c, e, e.get_tag());
            save_coercion_info(e, r);
            return r;
        }
        throw_kernel_exception(env(), e, [=](formatter const & fmt) { return pp_type_expected(fmt, e); });
    }

    /** \brief Similar to instantiate_rev, but assumes that subst contains only local constants.
        When replacing a variable with a local, we copy the local constant and inherit the tag
        associated with the variable. This is a trick for getter better error messages */
    expr instantiate_rev_locals(expr const & a, unsigned n, expr const * subst) {
        if (closed(a))
            return a;
        return replace(a, [=](expr const & m, unsigned offset) -> optional<expr> {
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
            });
    }

    expr visit_binding(expr e, expr_kind k, constraint_seq & cs) {
        scope_ctx scope(*this);
        buffer<expr> ds, ls, es;
        while (e.kind() == k) {
            es.push_back(e);
            expr d   = binding_domain(e);
            d = instantiate_rev_locals(d, ls.size(), ls.data());
            d = ensure_type(visit_expecting_type(d, cs), cs);
            ds.push_back(d);
            expr l   = mk_local(binding_name(e), d, binding_info(e));
            if (binding_info(e).is_contextual())
                m_context.add_local(l);
            m_full_context.add_local(l);
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
    expr visit_pi(expr const & e, constraint_seq & cs) { return visit_binding(e, expr_kind::Pi, cs); }
    expr visit_lambda(expr const & e, constraint_seq & cs) { return visit_binding(e, expr_kind::Lambda, cs); }

    expr visit_typed_expr(expr const & e, constraint_seq & cs) {
        constraint_seq t_cs;
        expr t      = visit(get_typed_expr_type(e), t_cs);
        constraint_seq v_cs;
        expr v      = visit(get_typed_expr_expr(e), v_cs);
        expr v_type = infer_type(v, v_cs);
        justification j = mk_justification(e, [=](formatter const & fmt, substitution const & subst) {
                substitution s(subst);
                format expected_fmt, given_fmt;
                std::tie(expected_fmt, given_fmt) = pp_until_different(fmt, s.instantiate(t), s.instantiate(v_type));
                format r("type mismatch at term");
                r += pp_indent_expr(fmt, s.instantiate(v));
                r += compose(line(), format("has type"));
                r += given_fmt;
                r += compose(line(), format("but is expected to have type"));
                r += expected_fmt;
                return r;
            });
        auto new_vcs    = ensure_has_type(v, v_type, t, j, m_relax_main_opaque);
        v = new_vcs.first;
        cs += t_cs + new_vcs.second + v_cs;
        return v;
    }

    expr visit_let_value(expr const & e, constraint_seq & cs) {
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

    expr visit_core(expr const & e, constraint_seq & cs) {
        if (is_placeholder(e)) {
            return visit_placeholder(e, cs);
        } else if (is_choice(e)) {
            return visit_choice(e, none_expr(), cs);
        } else if (is_let_value(e)) {
            return visit_let_value(e, cs);
        } else if (is_by(e)) {
            return visit_by(e, none_expr(), cs);
        } else if (is_no_info(e)) {
            flet<bool> let(m_no_info, true);
            return visit(get_annotation_arg(e), cs);
        } else if (is_typed_expr(e)) {
            return visit_typed_expr(e, cs);
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

    pair<expr, constraint_seq> visit(expr const & e) {
        if (is_extra_info(e)) {
            auto ecs = visit(get_annotation_arg(e));
            save_extra_type_data(e, ecs.first);
            return ecs;
        }
        expr r;
        expr b = e;
        constraint_seq cs;
        if (is_explicit(e)) {
            b    = get_explicit_arg(e);
            r    = visit_core(get_explicit_arg(e), cs);
        } else if (is_explicit(get_app_fn(e))) {
            r    = visit_core(e, cs);
        } else {
            if (is_implicit(e)) {
                r = get_implicit_arg(e);
                if (is_explicit(r)) r = get_explicit_arg(r);
                b = r;
                r = visit_core(r, cs);
            } else {
                r = visit_core(e, cs);
            }
            tag  g         = e.get_tag();
            expr r_type    = whnf(infer_type(r, cs), cs);
            expr imp_arg;
            bool is_strict = false;
            while (is_pi(r_type) && binding_info(r_type).is_implicit()) {
                imp_arg = mk_placeholder_meta(some_expr(binding_domain(r_type)), g, is_strict, cs);
                r       = mk_app(r, imp_arg, g);
                r_type  = whnf(instantiate(binding_body(r_type), imp_arg), cs);
            }
        }
        save_type_data(b, r);
        return mk_pair(r, cs);
    }

    expr visit(expr const & e, constraint_seq & cs) {
        auto r = visit(e);
        cs += r.second;
        return r.first;
    }

    unify_result_seq solve(constraint_seq const & cs) {
        buffer<constraint> tmp;
        cs.linearize(tmp);
        return unify(env(), tmp.size(), tmp.data(), m_ngen.mk_child(), m_unifier_config);
    }

    void display_unsolved_proof_state(expr const & mvar, proof_state const & ps, char const * msg) {
        lean_assert(is_metavar(mvar));
        if (!m_displayed_errors.contains(mlocal_name(mvar))) {
            m_displayed_errors.insert(mlocal_name(mvar));
            auto out = regular(env(), ios());
            flycheck_error err(out);
            display_error_pos(out, pip(), mvar);
            out << " unsolved placeholder, " << msg << "\n" << ps << endl;
        }
    }

    // For each occurrence of \c exact_tac in \c pre_tac, display its unassigned metavariables.
    // This is a trick to improve the quality of the error messages.
    void check_exact_tacs(expr const & pre_tac, substitution const & s) {
        for_each(pre_tac, [&](expr const & e, unsigned) {
                expr const & f = get_app_fn(e);
                if (is_constant(f) && const_name(f) == const_name(get_exact_tac_fn())) {
                    display_unassigned_mvars(e, s);
                    return false;
                } else {
                    return true;
                }
            });
    }

    optional<expr> get_pre_tactic_for(substitution & subst, expr const & mvar, name_set & visited) {
        if (auto it = m_local_tactic_hints.find(mlocal_name(mvar))) {
            expr pre_tac = subst.instantiate(*it);
            pre_tac = solve_unassigned_mvars(subst, pre_tac, visited);
            check_exact_tacs(pre_tac, subst);
            return some_expr(pre_tac);
        } else {
            return none_expr();
        }
    }

    optional<tactic> pre_tactic_to_tactic(expr const & pre_tac, expr const & mvar) {
        try {
            return optional<tactic>(expr_to_tactic(env(), pre_tac, pip()));
        } catch (expr_to_tactic_exception & ex) {
            auto out = regular(env(), ios());
            display_error_pos(out, pip(), mvar);
            out << " " << ex.what();
            out << pp_indent_expr(out.get_formatter(), pre_tac) << endl << "failed at:"
                << pp_indent_expr(out.get_formatter(), ex.get_expr()) << endl;
            return optional<tactic>();
        }
    }

    optional<tactic> get_local_tactic_hint(substitution & subst, expr const & mvar, name_set & visited) {
        if (auto pre_tac = get_pre_tactic_for(subst, mvar, visited)) {
            return pre_tactic_to_tactic(*pre_tac, mvar);
        } else {
            return optional<tactic>();
        }
    }

    /** \brief Try to instantiate meta-variable \c mvar (modulo its state ps) using the given tactic.
        If it succeeds, then update subst with the solution.
        Return true iff the metavariable \c mvar has been assigned.
    */
    bool try_using(substitution & subst, expr const & mvar, proof_state const & ps, tactic const & tac) {
        lean_assert(length(ps.get_goals()) == 1);
        // make sure ps is a really a proof state for mvar.
        lean_assert(mlocal_name(get_app_fn(head(ps.get_goals()).get_meta())) == mlocal_name(mvar));
        try {
            proof_state_seq seq = tac(env(), ios(), ps);
            auto r = seq.pull();
            if (!r) {
                // tactic failed to produce any result
                display_unsolved_proof_state(mvar, ps, "tactic failed");
                return false;
            } else if (!empty(r->first.get_goals())) {
                // tactic contains unsolved subgoals
                display_unsolved_proof_state(mvar, r->first, "unsolved subgoals");
                return false;
            } else {
                subst = r->first.get_subst();
                expr v = subst.instantiate(mvar);
                subst.assign(mlocal_name(mvar), v);
                return true;
            }
        } catch (tactic_exception & ex) {
            auto out = regular(env(), ios());
            display_error_pos(out, pip(), ex.get_expr());
            out << " tactic failed: " << ex.what() << "\n";
            return false;
        }
    }

    void solve_unassigned_mvar(substitution & subst, expr mvar, name_set & visited) {
        if (visited.contains(mlocal_name(mvar)))
            return;
        visited.insert(mlocal_name(mvar));
        if (auto local_hint = get_local_tactic_hint(subst, mvar, visited)) {
            auto meta = mvar_to_meta(mvar);
            if (!meta)
                return;
            meta = instantiate_meta(*meta, subst);
            // TODO(Leo): we are discarding constraints here
            expr type = m_tc[m_relax_main_opaque]->infer(*meta).first;
            // first solve unassigned metavariables in type
            type = solve_unassigned_mvars(subst, type, visited);
            proof_state ps(goals(goal(*meta, type)), subst, m_ngen.mk_child());
            try_using(subst, mvar, ps, *local_hint);
        }
    }

    expr solve_unassigned_mvars(substitution & subst, expr e, name_set & visited) {
        e = subst.instantiate(e);
        metavar_closure mvars(e);
        mvars.for_each_expr_mvar([&](expr const & mvar) {
                check_interrupted();
                solve_unassigned_mvar(subst, mvar, visited);
            });
        return subst.instantiate(e);
    }

    expr solve_unassigned_mvars(substitution & subst, expr const & e) {
        name_set visited;
        return solve_unassigned_mvars(subst, e, visited);
    }

    void display_unassigned_mvars(expr const & e, substitution const & s) {
        if (check_unassigned() && has_metavar(e)) {
            substitution tmp_s(s);
            for_each(e, [&](expr const & e, unsigned) {
                    if (!is_metavar(e))
                        return has_metavar(e);
                    if (auto it = mvar_to_meta(e)) {
                        expr meta      = tmp_s.instantiate(*it);
                        expr meta_type = tmp_s.instantiate(type_checker(env()).infer(meta).first);
                        goal g(meta, meta_type);
                        display_unsolved_proof_state(e, proof_state(goals(g), substitution(), m_ngen),
                                                     "don't know how to synthesize it");
                    }
                    return false;
                });
        }
    }

    /** \brief Apply substitution and solve remaining metavariables using tactics. */
    expr apply(substitution & s, expr const & e, name_set & univ_params, buffer<name> & new_params) {
        expr r = s.instantiate(e);
        if (has_univ_metavar(r))
            r = univ_metavars_to_params(env(), lls(), s, univ_params, new_params, r);
        r = solve_unassigned_mvars(s, r);
        display_unassigned_mvars(r, s);
        return r;
    }

    std::tuple<expr, level_param_names> apply(substitution & s, expr const & e) {
        auto ps = collect_univ_params(e);
        buffer<name> new_ps;
        expr r = apply(s, e, ps, new_ps);
        return std::make_tuple(r, to_list(new_ps.begin(), new_ps.end()));
    }

    std::tuple<expr, level_param_names> operator()(expr const & e, bool _ensure_type, bool relax_main_opaque) {
        flet<bool> set_relax(m_relax_main_opaque, relax_main_opaque && !get_hide_main_opaque(env()));
        constraint_seq cs;
        expr r = visit(e, cs);
        if (_ensure_type)
            r = ensure_type(r, cs);
        auto p  = solve(cs).pull();
        lean_assert(p);
        substitution s = p->first.first;
        auto result = apply(s, r);
        copy_info_to_manager(s);
        return result;
    }

    std::tuple<expr, expr, level_param_names> operator()(expr const & t, expr const & v, name const & n, bool is_opaque) {
        lean_assert(!has_local(t)); lean_assert(!has_local(v));
        constraint_seq t_cs;
        expr r_t      = ensure_type(visit(t, t_cs), t_cs);
        // Opaque definitions in the main module may treat other opaque definitions (in the main module) as transparent.
        flet<bool> set_relax(m_relax_main_opaque, is_opaque && !get_hide_main_opaque(env()));
        constraint_seq v_cs;
        expr r_v      = visit(v, v_cs);
        expr r_v_type = infer_type(r_v, v_cs);
        justification j = mk_justification(r_v, [=](formatter const & fmt, substitution const & subst) {
                substitution s(subst);
                return pp_def_type_mismatch(fmt, n, s.instantiate(r_t), s.instantiate(r_v_type));
            });
        pair<expr, constraint_seq> r_v_cs = ensure_has_type(r_v, r_v_type, r_t, j, is_opaque);
        r_v = r_v_cs.first;
        constraint_seq cs = t_cs + r_v_cs.second + v_cs;
        auto p  = solve(cs).pull();
        lean_assert(p);
        substitution s = p->first.first;
        name_set univ_params = collect_univ_params(r_v, collect_univ_params(r_t));
        buffer<name> new_params;
        expr new_r_t = apply(s, r_t, univ_params, new_params);
        expr new_r_v = apply(s, r_v, univ_params, new_params);
        copy_info_to_manager(s);
        return std::make_tuple(new_r_t, new_r_v, to_list(new_params.begin(), new_params.end()));
    }
};

static name g_tmp_prefix = name::mk_internal_unique_name();

std::tuple<expr, level_param_names> elaborate(elaborator_context & env, list<expr> const & ctx, expr const & e,
                                              bool relax_main_opaque, bool ensure_type) {
    return elaborator(env, ctx, name_generator(g_tmp_prefix))(e, ensure_type, relax_main_opaque);
}

std::tuple<expr, expr, level_param_names> elaborate(elaborator_context & env, name const & n, expr const & t, expr const & v,
                                                    bool is_opaque) {
    return elaborator(env, list<expr>(), name_generator(g_tmp_prefix))(t, v, n, is_opaque);
}
}
