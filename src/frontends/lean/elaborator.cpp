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
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/error_handling/error_handling.h"
#include "frontends/lean/local_decls.h"
#include "frontends/lean/class.h"
#include "frontends/lean/tactic_hint.h"

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

/** \brief Functional object for converting the universe metavariables in an expression in new universe parameters.
    The substitution is updated with the mapping metavar -> new param.
    The set of parameter names m_params and the buffer m_new_params are also updated.
*/
class univ_metavars_to_params_fn {
    environment const &        m_env;
    local_decls<level> const & m_lls;
    substitution &             m_subst;
    name_set &                 m_params;
    buffer<name> &             m_new_params;
    unsigned                   m_next_idx;

    /** \brief Create a new universe parameter s.t. the new name does not occur in \c m_params, nor it is
        a global universe in \e m_env or in the local_decls<level> m_lls.
        The new name is added to \c m_params, and the new level parameter is returned.
        The name is of the form "l_i" where \c i >= m_next_idx.
    */
    level mk_new_univ_param() {
        name l("l");
        name r = l.append_after(m_next_idx);
        while (m_lls.contains(r) || m_params.contains(r) || m_env.is_universe(r)) {
            m_next_idx++;
            r = l.append_after(m_next_idx);
        }
        m_params.insert(r);
        m_new_params.push_back(r);
        return mk_param_univ(r);
    }

public:
    univ_metavars_to_params_fn(environment const & env, local_decls<level> const & lls, substitution & s, name_set & ps, buffer<name> & new_ps):
        m_env(env), m_lls(lls), m_subst(s), m_params(ps), m_new_params(new_ps), m_next_idx(1) {}

    level apply(level const & l) {
        return replace(l, [&](level const & l) {
                if (!has_meta(l))
                    return some_level(l);
                if (is_meta(l)) {
                    if (auto it = m_subst.get_level(meta_id(l))) {
                        return some_level(*it);
                    } else {
                        level new_p = mk_new_univ_param();
                        m_subst.d_assign(l, new_p);
                        return some_level(new_p);
                    }
                }
                return none_level();
            });
    }

    expr apply(expr const & e) {
        if (!has_univ_metavar(e)) {
            return e;
        } else {
            return replace(e, [&](expr const & e) {
                    if (!has_univ_metavar(e)) {
                        return some_expr(e);
                    } else if (is_sort(e)) {
                        return some_expr(update_sort(e, apply(sort_level(e))));
                    } else if (is_constant(e)) {
                        levels ls = map(const_levels(e), [&](level const & l) { return apply(l); });
                        return some_expr(update_constant(e, ls));
                    } else {
                        return none_expr();
                    }
                });
        }
    }

    expr operator()(expr const & e) { return apply(e); }
};

/** \brief Helper class for implementing the \c elaborate functions. */
class elaborator {
    typedef list<expr> context;
    typedef std::vector<constraint> constraint_vect;
    typedef name_map<expr> local_tactic_hints;
    typedef name_map<expr> mvar2meta;
    typedef std::unique_ptr<type_checker> type_checker_ptr;

    environment         m_env;
    local_decls<level>  m_lls;
    io_state            m_ios;
    name_generator      m_ngen;
    type_checker_ptr    m_tc;
    substitution        m_subst;
    expr_map<expr>      m_cache; // (pointer equality) cache for Type and Constants (this is a trick to make sure we get the
                                 // same universe metavariable for different occurrences of the same Type/Constant
    context             m_ctx; // current local context: a list of local constants
    buffer<expr>        m_ctx_buffer; // m_ctx as a buffer
    buffer<expr>        m_ctx_domain_buffer; // m_ctx_domain_buffer[i] == abstract_locals(m_ctx_buffer[i], i, m_ctx_buffer.begin())
    pos_info_provider * m_pos_provider; // optional expression position information used when reporting errors.
    justification       m_accumulated; // accumulate justification of eagerly used substitutions
    constraint_vect     m_constraints; // constraints that must be solved for the elaborated term to be type correct.
    local_tactic_hints  m_local_tactic_hints; // mapping from metavariable name ?m to tactic expression that should be used to solve it.
                                              // this mapping is populated by the 'by tactic-expr' expression.
    mvar2meta           m_mvar2meta; // mapping from metavariable ?m to the (?m l_1 ... l_n) where [l_1 ... l_n] are the local constants
                                     // representing the context where ?m was created.
    name_set            m_displayed_errors; // set of metavariables that we already reported unsolved/unassigned
    bool                m_check_unassigned; // if true if display error messages if elaborated term still contains metavariables
    bool                m_use_local_instances; // if true class-instance resolution will use the local context

    // Set m_ctx to ctx, and make sure m_ctx_buffer and m_ctx_domain_buffer reflect the contents of the new ctx
    void set_ctx(context const & ctx) {
        m_ctx = ctx;
        m_ctx_buffer.clear();
        m_ctx_domain_buffer.clear();
        to_buffer(ctx, m_ctx_buffer);
        std::reverse(m_ctx_buffer.begin(), m_ctx_buffer.end());
        for (unsigned i = 0; i < m_ctx_buffer.size(); i++) {
            m_ctx_domain_buffer.push_back(abstract_locals(m_ctx_buffer[i], i, m_ctx_buffer.data()));
        }
    }

    /** \brief Auxiliary object for creating backtracking points.
        \remark A scope can only be created when m_constraints and m_subst are empty,
        and m_accumulated is none.
    */
    struct scope {
        elaborator & m_main;
        context      m_old_ctx;
        scope(elaborator & e, context const & ctx, substitution const & s):m_main(e) {
            lean_assert(m_main.m_constraints.empty());
            lean_assert(m_main.m_accumulated.is_none());
            m_old_ctx    = m_main.m_ctx;
            m_main.set_ctx(ctx);
            m_main.m_tc->push();
            m_main.m_subst = s;
        }
        ~scope() {
            m_main.set_ctx(m_old_ctx);
            m_main.m_tc->pop();
            m_main.m_constraints.clear();
            m_main.m_accumulated = justification();
            m_main.m_subst = substitution();
            lean_assert(m_main.m_constraints.empty());
            lean_assert(m_main.m_accumulated.is_none());
        }
    };

    /* \brief Move all constraints generated by the type checker to the buffer m_constraints. */
    void consume_tc_cnstrs() {
        while (auto c = m_tc->next_cnstr())
            m_constraints.push_back(*c);
    }

    struct choice_elaborator {
        bool m_ignore_failure;
        choice_elaborator(bool ignore_failure = false):m_ignore_failure(ignore_failure) {}
        virtual optional<constraints> next() = 0;
    };

    /** \brief 'Choice' expressions <tt>(choice e_1 ... e_n)</tt> are mapped into a metavariable \c ?m
        and a choice constraints <tt>(?m in fn)</tt> where \c fn is a choice function.
        The choice function produces a stream of alternatives. In this case, it produces a stream of
        size \c n, one alternative for each \c e_i.
        This is a helper class for implementing this choice functions.
    */
    struct choice_expr_elaborator : public choice_elaborator {
        elaborator & m_elab;
        expr         m_mvar;
        expr         m_choice;
        context      m_ctx;
        substitution m_subst;
        unsigned     m_idx;
        choice_expr_elaborator(elaborator & elab, expr const & mvar, expr const & c, context const & ctx, substitution const & s):
            m_elab(elab), m_mvar(mvar), m_choice(c), m_ctx(ctx), m_subst(s), m_idx(0) {
        }

        virtual optional<constraints> next() {
            while (m_idx < get_num_choices(m_choice)) {
                expr const & c = get_choice(m_choice, m_idx);
                m_idx++;
                try {
                    scope s(m_elab, m_ctx, m_subst);
                    expr r = m_elab.visit(c);
                    justification j = m_elab.m_accumulated;
                    m_elab.consume_tc_cnstrs();
                    list<constraint> cs = to_list(m_elab.m_constraints.begin(), m_elab.m_constraints.end());
                    cs = cons(mk_eq_cnstr(m_mvar, r, j), cs);
                    return optional<constraints>(cs);
                } catch (exception &) {}
            }
            return optional<constraints>();
        }
    };

    /** \brief Whenever the elaborator finds a placeholder '_' or introduces an implicit argument, it creates
        a metavariable \c ?m. It also creates a delayed choice constraint (?m in fn).

        The function \c fn produces a stream of alternative solutions for ?m.
        In this case, \c fn will do the following:
          1) if the elaborated type of ?m is a 'class' C, then the stream will start with
                  a) all local instances of class C (if elaborator.local_instances == true)
                  b) solutions produced by tactic_hints for class C
          2) if the elaborated type of ?m is not a class, then the stream will only contain
             the solutions produced by tactic_hints.

        The unifier only process delayed choice constraints when there are no other kind of constraint to be
        processed.

        This is a helper class for implementing this choice function.
    */
    struct placeholder_elaborator : public choice_elaborator {
        elaborator &            m_elab;
        expr                    m_meta;
        expr                    m_meta_type; // elaborated type of the metavariable
        list<expr>              m_local_instances; // local instances that should also be included in the class-instance resolution.
        list<name>              m_instances; // global declaration names that are class instances.
                                             // This information is retrieved using #get_class_instances.
        list<tactic_hint_entry> m_tactics;
        proof_state_seq         m_tactic_result; // result produce by last executed tactic.
        buffer<expr>            m_mvars_in_meta_type; // metavariables that occur in m_meta_type, the tactics may instantiate some of them
        context                 m_ctx; // local context for m_meta
        substitution            m_subst;
        justification           m_jst;

        placeholder_elaborator(elaborator & elab, expr const & meta, expr const & meta_type,
                               list<expr> const & local_insts, list<name> const & instances, list<tactic_hint_entry> const & tacs,
                               context const & ctx, substitution const & s, justification const & j, bool ignore_failure):
            choice_elaborator(ignore_failure),
            m_elab(elab), m_meta(meta), m_meta_type(meta_type), m_local_instances(local_insts), m_instances(instances),
            m_tactics(tacs), m_ctx(ctx), m_subst(s), m_jst(j) {
            collect_metavars(meta_type, m_mvars_in_meta_type);
        }

        optional<constraints> try_instance(name const & inst) {
            auto decl   = m_elab.m_env.find(inst);
            if (!decl)
                return optional<constraints>();
            expr type   = decl->get_type();
            // create the term pre (inst _ ... _)
            expr pre    = copy_tag(m_meta, mk_explicit(copy_tag(m_meta, mk_constant(inst))));
            while (is_pi(type)) {
                type = binding_body(type);
                pre  = copy_tag(m_meta, ::lean::mk_app(pre, copy_tag(m_meta, mk_strict_expr_placeholder())));
            }
            try {
                scope s(m_elab, m_ctx, m_subst);
                expr r = m_elab.visit(pre); // use elaborator to create metavariables, levels, etc.
                justification j = m_elab.m_accumulated;
                m_elab.consume_tc_cnstrs();
                for (auto & c : m_elab.m_constraints)
                    c = update_justification(c, mk_composite1(m_jst, c.get_justification()));
                list<constraint> cs = to_list(m_elab.m_constraints.begin(), m_elab.m_constraints.end());
                cs = cons(mk_eq_cnstr(m_meta, r, mk_composite1(m_jst, j)), cs);
                return optional<constraints>(cs);
            } catch (exception &) {
                return optional<constraints>();
            }
        }

        optional<constraints> get_next_tactic_result() {
            while (auto next = m_tactic_result.pull()) {
                m_tactic_result = next->second;
                if (!empty(next->first.get_goals()))
                    continue; // has unsolved goals
                substitution subst = next->first.get_subst();
                buffer<constraint> cs;
                expr const & mvar = get_app_fn(m_meta);
                cs.push_back(mk_eq_cnstr(mvar, subst.instantiate(mvar), m_jst));
                for (auto const & mvar : m_mvars_in_meta_type)
                    cs.push_back(mk_eq_cnstr(mvar, subst.instantiate(mvar), m_jst));
                return optional<constraints>(to_list(cs.begin(), cs.end()));
            }
            return optional<constraints>();
        }

        virtual optional<constraints> next() {
            while (!empty(m_local_instances)) {
                expr inst         = head(m_local_instances);
                m_local_instances = tail(m_local_instances);
                constraints cs(mk_eq_cnstr(m_meta, inst, m_jst));
                return optional<constraints>(cs);
            }
            while (!empty(m_instances)) {
                name inst   = head(m_instances);
                m_instances = tail(m_instances);
                if (auto cs = try_instance(inst))
                    return cs;
            }
            if (auto cs = get_next_tactic_result())
                return cs;
            while (!empty(m_tactics)) {
                tactic const & tac = head(m_tactics).get_tactic();
                m_tactics          = tail(m_tactics);
                proof_state ps(goals(goal(m_meta, m_meta_type)), m_subst, m_elab.m_ngen.mk_child());
                try {
                    m_tactic_result    = tac(m_elab.m_env, m_elab.m_ios, ps);
                    if (auto cs = get_next_tactic_result())
                        return cs;
                } catch (exception &) {}
            }
            return optional<constraints>();
        }
    };

    lazy_list<constraints> choose(std::shared_ptr<choice_elaborator> c) {
        return mk_lazy_list<constraints>([=]() {
                auto s = c->next();
                if (s) {
                    return some(mk_pair(*s, choose(c)));
                } else if (c->m_ignore_failure) {
                    // return singleton empty list of constraints, and let tactic hints try to instantiate the metavariable.
                    return lazy_list<constraints>::maybe_pair(constraints(), lazy_list<constraints>());
                } else {
                    return lazy_list<constraints>::maybe_pair();
                }
            });
    }

public:
    elaborator(environment const & env, local_decls<level> const & lls, list<expr> const & ctx, io_state const & ios, name_generator const & ngen,
               pos_info_provider * pp, bool check_unassigned):
        m_env(env), m_lls(lls), m_ios(ios),
        m_ngen(ngen), m_tc(mk_type_checker_with_hints(env, m_ngen.mk_child())),
        m_pos_provider(pp) {
        m_check_unassigned = check_unassigned;
        m_use_local_instances = get_elaborator_local_instances(ios.get_options());
        set_ctx(ctx);
    }

    expr mk_local(name const & n, expr const & t, binder_info const & bi) {
        return ::lean::mk_local(m_ngen.next(), n, t, bi);
    }

    expr infer_type(expr const & e) {
        lean_assert(closed(e));
        return m_tc->infer(e); }

    expr whnf(expr const & e) {
        return m_tc->whnf(e);
    }

    /** \brief Clear constraint buffer \c m_constraints, and associated datastructures
        \c m_subst and \c m_accumulated.

        \remark \c m_subst contains solutions obtained by eagerly solving the "easy" constraints
        in \c m_subst, and \c m_accumulated store the justifications of all substitutions eagerly
        applied.
    */
    void clear_constraints() {
        m_constraints.clear();
        m_subst = substitution();
        m_accumulated = justification();
    }

    void add_cnstr_core(constraint const & c) {
        m_constraints.push_back(c);
    }

    /** \brief Add \c c to \c m_constraints, but also tries to update \c m_subst using \c c.
        The idea is to "populate" \c m_subst using easy/simple constraints.
        This trick improves the number of places where coercions can be applied.
        In the future, we may also use this information to implement eager pruning of choice
        constraints.

        \remark The justification \c m_accumulated is "appended" to \c c.
        This justification justifies all substitutions used.

        \remark By appeding \c m_accumulated we know we are not missing any dependency,
        but this is a coarse approximation of that actual dependencies.
    */
    void add_cnstr(constraint c) {
        if (!m_accumulated.is_none())
            c = update_justification(c, mk_composite1(c.get_justification(), m_accumulated));
        add_cnstr_core(c);
        auto ss = unify_simple(m_subst, c);
        m_subst = ss.second;
        if (ss.first == unify_status::Failed)
            throw unifier_exception(c.get_justification(), m_subst);
    }

    /** \brief Eagerly instantiate metavars using \c m_subst.
        \remark We update \c m_accumulated with any justifications used.
    */
    expr instantiate_metavars(expr const & e) {
        auto e_j = m_subst.instantiate_metavars(e);
        m_accumulated = mk_composite1(m_accumulated, e_j.second);
        return e_j.first;
    }

    static expr save_tag(expr && e, tag g) {
        e.set_tag(g);
        return e;
    }

    expr mk_app(expr const & f, expr const & a, tag g) {
        return save_tag(::lean::mk_app(f, a), g);
    }

    /** \brief Given <tt>e[l_1, ..., l_n]</tt> and assuming \c m_ctx is
               <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
         then the result is
               <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), e[x_1, ... x_n])</tt>.
    */
    expr pi_abstract_context(expr e, tag g) {
        e = abstract_locals(e, m_ctx_buffer.size(), m_ctx_buffer.data());
        unsigned i = m_ctx_domain_buffer.size();
        while (i > 0) {
            --i;
            expr const & l = m_ctx_domain_buffer[i];
            e = save_tag(mk_pi(local_pp_name(l), mlocal_type(l), e, local_info(l)), g);
        }
        return e;
    }

    /** \brief Assuming \c m_ctx is
           <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
        return <tt>(f l_1 ... l_n)</tt>.
    */
    expr apply_context(expr const & f, tag g) {
        expr r = f;
        for (unsigned i = 0; i < m_ctx_buffer.size(); i++)
            r = mk_app(r, m_ctx_buffer[i], g);
        return r;
    }

    /** \brief Assuming \c m_ctx is
           <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
        return a fresh metavariable \c ?m with type
           <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{?u})</tt>,
        where \c ?u is a fresh universe metavariable.
    */
    expr mk_type_metavar(tag g) {
        name n = m_ngen.next();
        expr s = save_tag(mk_sort(mk_meta_univ(m_ngen.next())), g);
        expr t = pi_abstract_context(s, g);
        return save_tag(::lean::mk_metavar(n, t), g);
    }

    /** \brief Assuming \c m_ctx is
            <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
        return <tt>(?m l_1 ... l_n)</tt> where \c ?m is a fresh metavariable with type
            <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{?u})</tt>,
        and \c ?u is a fresh universe metavariable.

       \remark The type of the resulting expression is <tt>Type.{?u}</tt>
    */
    expr mk_type_meta(tag g) {
        return apply_context(mk_type_metavar(g), g);
    }

    /** \brief Given <tt>type[l_1, ..., l_n]</tt> and assuming \c m_ctx is
            <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
        then the result is a fresh metavariable \c ?m with type
            <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), type[x_1, ... x_n])</tt>.
        If <tt>type</tt> is none, then the result is a fresh metavariable \c ?m1 with type
            <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), ?m2 x1 .... xn)</tt>,
        where ?m2 is another fresh metavariable with type
            <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{?u})</tt>,
        and \c ?u is a fresh universe metavariable.
    */
    expr mk_metavar(optional<expr> const & type, tag g) {
        name n      = m_ngen.next();
        expr r_type = type ? *type : mk_type_meta(g);
        expr t      = pi_abstract_context(r_type, g);
        return save_tag(::lean::mk_metavar(n, t), g);
    }

    /** \brief Given <tt>type[l_1, ..., l_n]</tt> and assuming \c m_ctx is
           <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
        return (?m l_1 ... l_n), where ?m is a fresh metavariable
        created using \c mk_metavar.

        \see mk_metavar
    */
    expr mk_meta(optional<expr> const & type, tag g) {
        expr mvar = mk_metavar(type, g);
        expr meta = apply_context(mvar, g);
        m_mvar2meta.insert(mlocal_name(mvar), meta);
        return meta;
    }

    list<name> get_class_instances(expr const & type) {
        if (is_constant(get_app_fn(type))) {
            name const & c = const_name(get_app_fn(type));
            return ::lean::get_class_instances(m_env, c);
        } else {
            return list<name>();
        }
    }

    bool is_class(expr const & type) {
        expr f = get_app_fn(type);
        if (!is_constant(f))
            return false;
        name const & cls_name = const_name(f);
        return ::lean::is_class(m_env, cls_name) || !empty(get_tactic_hints(m_env, cls_name));
    }

    static expr instantiate_meta(expr const & meta, substitution const & subst) {
        buffer<expr> locals;
        expr mvar = get_app_args(meta, locals);
        mvar = update_mlocal(mvar, subst.instantiate(mlocal_type(mvar)));
        for (auto & local : locals) local = subst.instantiate(local);
        return ::lean::mk_app(mvar, locals);
    }

    /** \brief Return a 'failed to synthesize placholder' justification for the given
        metavariable application \c m of the form (?m l_1 ... l_k) */
    justification mk_failed_to_synthesize_jst(expr const & m) {
        environment env = m_env;
        return mk_justification(m, [=](formatter const & fmt, substitution const & subst) {
                expr new_m    = instantiate_meta(m, subst);
                expr new_type = type_checker(env).infer(new_m);
                proof_state ps(goals(goal(new_m, new_type)), substitution(), name_generator("dontcare"));
                return format({format("failed to synthesize placeholder"), line(), ps.pp(fmt)});
            });
    }

    /** \brief Return a list of instances of the class \c cls_name that occur in \c ctx */
    static list<expr> get_local_instances(context ctx, name const & cls_name) {
        buffer<expr> buffer;
        for (auto const & l : ctx) {
            if (!is_local(l))
                continue;
            expr inst_type    = mlocal_type(l);
            if (!is_constant(get_app_fn(inst_type)) || const_name(get_app_fn(inst_type)) != cls_name)
                continue;
            buffer.push_back(l);
        }
        return to_list(buffer.begin(), buffer.end());
    }

    /** \brief Create a metavariable, and attach choice constraint for generating
        solutions using class-instances and tactic-hints.
    */
    expr mk_placeholder_meta(optional<expr> const & type, tag g, bool is_strict = false) {
        expr m = mk_meta(type, g);
        context ctx     = m_ctx;
        justification j = mk_failed_to_synthesize_jst(m);
        auto choice_fn = [=](expr const & meta, expr const & meta_type, substitution const & s, name_generator const & /* ngen */) {
            expr const & mvar = get_app_fn(meta);
            if (is_class(meta_type)) {
                name const & cls_name = const_name(get_app_fn(meta_type));
                list<expr> local_insts;
                if (m_use_local_instances)
                    local_insts = get_local_instances(ctx, cls_name);
                list<name>  insts = get_class_instances(meta_type);
                list<tactic_hint_entry> tacs;
                if (!s.is_assigned(mvar))
                    tacs = get_tactic_hints(m_env, cls_name);
                if (empty(local_insts) && empty(insts) && empty(tacs))
                    return lazy_list<constraints>(); // nothing to be done
                bool ignore_failure = false; // we are always strict with placeholders associated with classes
                return choose(std::make_shared<placeholder_elaborator>(*this, meta, meta_type, local_insts, insts, tacs, ctx, s, j,
                                                                       ignore_failure));
            } else if (s.is_assigned(mvar)) {
                // if the metavariable is assigned and it is not a class, then we just ignore it, and return
                // the an empty set of constraints.
                return lazy_list<constraints>(constraints());
            } else {
                list<tactic_hint_entry> tacs = get_tactic_hints(m_env);
                bool ignore_failure = !is_strict;
                return choose(std::make_shared<placeholder_elaborator>(*this, meta, meta_type, list<expr>(), list<name>(), tacs, ctx, s, j,
                                                                       ignore_failure));
            }
        };
        add_cnstr(mk_choice_cnstr(m, choice_fn, to_delay_factor(cnstr_group::MaxDelayed), j));
        return m;
    }

    /** \brief Convert the metavariable to the metavariable application that captures
        the context where it was defined.
    */
    optional<expr> mvar_to_meta(expr mvar) {
        if (auto it = m_mvar2meta.find(mlocal_name(mvar)))
            return some_expr(*it);
        else
            return none_expr();
    }

    expr visit_expecting_type(expr const & e) {
        if (is_placeholder(e) && !placeholder_type(e))
            return mk_type_meta(e.get_tag());
        else
            return visit(e);
    }

    expr visit_expecting_type_of(expr const & e, expr const & t) {
        if (is_placeholder(e) && !placeholder_type(e))
            return mk_placeholder_meta(some_expr(t), e.get_tag(), is_strict_placeholder(e));
        else if (is_choice(e))
            return visit_choice(e, some_expr(t));
        else if (is_by(e))
            return visit_by(e, some_expr(t));
        else
            return visit(e);
    }

    expr visit_choice(expr const & e, optional<expr> const & t) {
        lean_assert(is_choice(e));
        // Possible optimization: try to lookahead and discard some of the alternatives.
        expr m      = mk_meta(t, e.get_tag());
        context ctx = m_ctx;
        auto fn = [=](expr const & mvar, expr const & /* type */, substitution const & s, name_generator const & /* ngen */) {
            return choose(std::make_shared<choice_expr_elaborator>(*this, mvar, e, ctx, s));
        };
        justification j = mk_justification("none of the overloads is applicable", some_expr(e));
        add_cnstr(mk_choice_cnstr(m, fn, to_delay_factor(cnstr_group::Basic), j));
        return m;
    }

    expr visit_by(expr const & e, optional<expr> const & t) {
        lean_assert(is_by(e));
        expr tac = visit(get_by_arg(e));
        expr m   = mk_meta(t, e.get_tag());
        m_local_tactic_hints.insert(mlocal_name(get_app_fn(m)), tac);
        return m;
    }

    /** \brief Make sure \c f is really a function, if it is not, try to apply coercions.
        The result is a pair <tt>new_f, f_type</tt>, where new_f is the new value for \c f,
        and \c f_type is its type (and a Pi-expression)
    */
    std::pair<expr, expr> ensure_fun(expr f) {
        expr f_type = infer_type(f);
        if (!is_pi(f_type))
            f_type = whnf(f_type);
        if (!is_pi(f_type) && has_metavar(f_type)) {
            f_type = whnf(instantiate_metavars(f_type));
            if (!is_pi(f_type) && is_meta(f_type)) {
                // let type checker add constraint
                f_type = m_tc->ensure_pi(f_type, f);
            }
        }
        if (!is_pi(f_type)) {
            // try coercion to function-class
            optional<expr> c = get_coercion_to_fun(m_env, f_type);
            if (c) {
                f = mk_app(*c, f, f.get_tag());
                f_type = infer_type(f);
                lean_assert(is_pi(f_type));
            } else {
                throw_kernel_exception(m_env, f, [=](formatter const & fmt) { return pp_function_expected(fmt, f); });
            }
        }
        lean_assert(is_pi(f_type));
        return mk_pair(f, f_type);
    }

    bool has_coercions_from(expr const & a_type) {
        expr const & a_cls = get_app_fn(whnf(a_type));
        return is_constant(a_cls) && ::lean::has_coercions_from(m_env, const_name(a_cls));
    }

    bool has_coercions_to(expr const & d_type) {
        expr const & d_cls = get_app_fn(whnf(d_type));
        return is_constant(d_cls) && ::lean::has_coercions_to(m_env, const_name(d_cls));
    }

    expr apply_coercion(expr const & a, expr a_type, expr d_type) {
        a_type = whnf(a_type);
        d_type = whnf(d_type);
        expr const & d_cls = get_app_fn(d_type);
        if (is_constant(d_cls)) {
            if (auto c = get_coercion(m_env, a_type, const_name(d_cls)))
                return mk_app(*c, a, a.get_tag());
        }
        return a;
    }

    constraint mk_delayed_coercion_cnstr(expr const & m, expr const & a, expr const & a_type, justification const & j, unsigned delay_factor) {
        auto choice_fn = [=](expr const & mvar, expr const & new_d_type, substitution const & /* s */, name_generator const & /* ngen */) {
            // Remark: we want the coercions solved before we start discarding FlexFlex constraints. So, we use PreFlexFlex as a max cap
            // for delaying coercions.
            if (is_meta(new_d_type) && delay_factor < to_delay_factor(cnstr_group::PreFlexFlex)) {
                // The type is still unknown, delay the constraint even more.
                return lazy_list<constraints>(constraints(mk_delayed_coercion_cnstr(m, a, a_type, justification(), delay_factor+1)));
            } else {
                expr r = apply_coercion(a, a_type, new_d_type);
                return lazy_list<constraints>(constraints(mk_eq_cnstr(mvar, r, justification())));
            }
        };
        return mk_choice_cnstr(m, choice_fn, delay_factor, j);
    }

    /** \brief Given an application \c e, where the expected type is d_type, and the argument type is a_type,
        create a "delayed coercion". The idea is to create a choice constraint and postpone the coercion
        search. We do that whenever d_type or a_type is a metavar application, and d_type or a_type is a coercion source/target.
    */
    expr mk_delayed_coercion(expr const & e, expr const & d_type, expr const & a_type) {
        expr a = app_arg(e);
        expr m = mk_meta(some_expr(d_type), a.get_tag());
        justification j = mk_app_justification(e, d_type, a_type);
        add_cnstr(mk_delayed_coercion_cnstr(m, a, a_type, j, to_delay_factor(cnstr_group::Basic)));
        return update_app(e, app_fn(e), m);
    }

    expr visit_app(expr const & e) {
        bool expl   = is_explicit(get_app_fn(e));
        expr f      = visit(app_fn(e));
        auto f_t    = ensure_fun(f);
        f           = f_t.first;
        expr f_type = f_t.second;
        lean_assert(is_pi(f_type));
        if (!expl) {
            while (binding_info(f_type).is_strict_implicit()) {
                tag g        = f.get_tag();
                expr imp_arg = mk_placeholder_meta(some_expr(binding_domain(f_type)), g);
                f            = mk_app(f, imp_arg, g);
                auto f_t     = ensure_fun(f);
                f            = f_t.first;
                f_type       = f_t.second;
            }
        }
        expr d_type = binding_domain(f_type);
        expr a      = visit_expecting_type_of(app_arg(e), d_type);
        expr a_type = instantiate_metavars(infer_type(a));
        expr r      = mk_app(f, a, e.get_tag());

        if (is_meta(d_type) && has_coercions_from(a_type)) {
            return mk_delayed_coercion(r, d_type, a_type);
        } else if (is_meta(a_type) && has_coercions_to(d_type)) {
            return mk_delayed_coercion(r, d_type, a_type);
        } else {
            app_delayed_justification j(r, f_type, a_type);
            if (!m_tc->is_def_eq(a_type, d_type, j)) {
                expr new_a = apply_coercion(a, a_type, d_type);
                bool coercion_worked = false;
                if (!is_eqp(a, new_a)) {
                    expr new_a_type = instantiate_metavars(infer_type(new_a));
                    coercion_worked = m_tc->is_def_eq(new_a_type, d_type, j);
                }
                if (coercion_worked) {
                    r = update_app(r, f, new_a);
                } else {
                    if (has_metavar(a_type) || has_metavar(d_type)) {
                        // rely on unification hints to solve this constraint
                        add_cnstr(mk_eq_cnstr(a_type, d_type, j.get()));
                    } else {
                        throw_kernel_exception(m_env, a, [=](formatter const & fmt) { return pp_app_type_mismatch(fmt, e, d_type, a_type); });
                    }
                }
            }
            return r;
        }
    }

    expr visit_placeholder(expr const & e) {
        return mk_placeholder_meta(placeholder_type(e), e.get_tag(), is_strict_placeholder(e));
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
        auto it = m_cache.find(e);
        if (it != m_cache.end()) {
            return it->second;
        } else {
            expr r = update_sort(e, replace_univ_placeholder(sort_level(e)));
            m_cache.insert(mk_pair(e, r));
            return r;
        }
    }

    expr visit_macro(expr const & e) {
        if (is_as_is(e)) {
            return get_as_is_arg(e);
        } else {
            // Remark: Macros are not meant to be used in the front end.
            // Perhaps, we should throw error.
            buffer<expr> args;
            for (unsigned i = 0; i < macro_num_args(e); i++)
                args.push_back(visit(macro_arg(e, i)));
            return update_macro(e, args.size(), args.data());
        }
    }

    expr visit_constant(expr const & e) {
        auto it = m_cache.find(e);
        if (it != m_cache.end()) {
            return it->second;
        } else {
            declaration d = m_env.get(const_name(e));
            buffer<level> ls;
            for (level const & l : const_levels(e))
                ls.push_back(replace_univ_placeholder(l));
            unsigned num_univ_params = length(d.get_univ_params());
            if (num_univ_params < ls.size())
                throw_kernel_exception(m_env, sstream() << "incorrect number of universe levels parameters for '" << const_name(e) << "', #"
                                       << num_univ_params << " expected, #" << ls.size() << " provided");
            // "fill" with meta universe parameters
            for (unsigned i = ls.size(); i < num_univ_params; i++)
                ls.push_back(mk_meta_univ(m_ngen.next()));
            lean_assert(num_univ_params == ls.size());
            expr r = update_constant(e, to_list(ls.begin(), ls.end()));
            m_cache.insert(mk_pair(e, r));
            return r;
        }
    }

    /** \brief Make sure \c e is a type. If it is not, then try to apply coercions. */
    expr ensure_type(expr const & e) {
        expr t = infer_type(e);
        if (is_sort(t))
            return e;
        t = whnf(t);
        if (is_sort(t))
            return e;
        if (has_metavar(t)) {
            t = whnf(instantiate_metavars(t));
            if (is_sort(t))
                return e;
            if (is_meta(t)) {
                // let type checker add constraint
                m_tc->ensure_sort(t, e);
                return e;
            }
        }
        optional<expr> c = get_coercion_to_sort(m_env, t);
        if (c)
            return mk_app(*c, e, e.get_tag());
        throw_kernel_exception(m_env, e, [=](formatter const & fmt) { return pp_type_expected(fmt, e); });
    }

    struct scope_ctx {
        elaborator & m_main;
        context      m_old_ctx;
        unsigned     m_old_sz;
        scope_ctx(elaborator & main):m_main(main), m_old_ctx(main.m_ctx), m_old_sz(main.m_ctx_buffer.size()) {}
        ~scope_ctx() {
            m_main.m_ctx = m_old_ctx;
            m_main.m_ctx_buffer.shrink(m_old_sz);
            m_main.m_ctx_domain_buffer.shrink(m_old_sz);
        }
    };

    void add_local(expr const & l) {
        m_ctx = cons(l, m_ctx);
        m_ctx_domain_buffer.push_back(abstract_locals(l, m_ctx_buffer.size(), m_ctx_buffer.data()));
        m_ctx_buffer.push_back(l);
    }

    expr visit_binding(expr e, expr_kind k) {
        scope_ctx scope(*this);
        buffer<expr> ds, ls, es;
        while (e.kind() == k) {
            es.push_back(e);
            expr d   = binding_domain(e);
            d = instantiate_rev(d, ls.size(), ls.data());
            d = ensure_type(visit_expecting_type(d));
            ds.push_back(d);
            expr l   = mk_local(binding_name(e), d, binding_info(e));
            if (binding_info(e).is_contextual())
                add_local(l);
            ls.push_back(l);
            e = binding_body(e);
        }
        lean_assert(ls.size() == es.size() && ls.size() == ds.size());
        e = instantiate_rev(e, ls.size(), ls.data());
        e = (k == expr_kind::Pi) ? ensure_type(visit_expecting_type(e)) : visit(e);
        e = abstract_locals(e, ls.size(), ls.data());
        unsigned i = ls.size();
        while (i > 0) {
            --i;
            e = update_binding(es[i], abstract_locals(ds[i], i, ls.data()), e);
        }
        return e;
    }
    expr visit_pi(expr const & e) { return visit_binding(e, expr_kind::Pi); }
    expr visit_lambda(expr const & e) { return visit_binding(e, expr_kind::Lambda); }

    expr visit_core(expr const & e) {
        if (is_placeholder(e)) {
            return visit_placeholder(e);
        } else if (is_choice(e)) {
            return visit_choice(e, none_expr());
        } else if (is_by(e)) {
            return visit_by(e, none_expr());
        } else {
            switch (e.kind()) {
            case expr_kind::Local:      return e;
            case expr_kind::Meta:       return e;
            case expr_kind::Sort:       return visit_sort(e);
            case expr_kind::Var:        lean_unreachable();  // LCOV_EXCL_LINE
            case expr_kind::Constant:   return visit_constant(e);
            case expr_kind::Macro:      return visit_macro(e);
            case expr_kind::Lambda:     return visit_lambda(e);
            case expr_kind::Pi:         return visit_pi(e);
            case expr_kind::App:        return visit_app(e);
            }
            lean_unreachable(); // LCOV_EXCL_LINE
        }
    }

    expr visit(expr const & e) {
        expr r;
        if (is_explicit(e)) {
            r    = visit_core(get_explicit_arg(e));
        } else if (is_explicit(get_app_fn(e))) {
            r    = visit_core(e);
        } else {
            if (is_implicit(e)) {
                r = get_implicit_arg(e);
                if (is_explicit(r)) r = get_explicit_arg(r);
                r = visit_core(r);
            } else {
                r = visit_core(e);
            }
            if (!is_lambda(r)) {
                tag  g      = e.get_tag();
                expr r_type = whnf(infer_type(r));
                expr imp_arg;
                while (is_pi(r_type) && binding_info(r_type).is_implicit()) {
                    imp_arg = mk_placeholder_meta(some_expr(binding_domain(r_type)), g);
                    r       = mk_app(r, imp_arg, g);
                    r_type  = whnf(instantiate(binding_body(r_type), imp_arg));
                }
            }
        }
        return r;
    }

    lazy_list<substitution> solve() {
        consume_tc_cnstrs();
        buffer<constraint> cs;
        cs.append(m_constraints);
        m_constraints.clear();
        return unify(m_env, cs.size(), cs.data(), m_ngen.mk_child(), true, m_ios.get_options());
    }

    static void collect_metavars(expr const & e, buffer<expr> & mvars) {
        for_each(e, [&](expr const & e, unsigned) {
                if (is_metavar(e)) {
                    mvars.push_back(e);
                    return false; /* do not visit its type */
                }
                return has_metavar(e);
            });
    }

    void display_unsolved_proof_state(expr const & mvar, proof_state const & ps, char const * msg) {
        lean_assert(is_metavar(mvar));
        if (!m_displayed_errors.contains(mlocal_name(mvar))) {
            m_displayed_errors.insert(mlocal_name(mvar));
            auto out = regular(m_env, m_ios);
            display_error_pos(out, m_pos_provider, mvar);
            out << " unsolved placeholder, " << msg << "\n" << ps << "\n";
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
            // TODO(Leo): m_env tactic hints
            return none_expr();
        }
    }

    optional<tactic> pre_tactic_to_tactic(expr const & pre_tac, expr const & mvar) {
        try {
            return optional<tactic>(expr_to_tactic(m_env, pre_tac, m_pos_provider));
        } catch (expr_to_tactic_exception & ex) {
            auto out = regular(m_env, m_ios);
            display_error_pos(out, m_pos_provider, mvar);
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
            proof_state_seq seq = tac(m_env, m_ios, ps);
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
                subst = subst.assign(mlocal_name(mvar), v);
                return true;
            }
        } catch (tactic_exception & ex) {
            auto out = regular(m_env, m_ios);
            display_error_pos(out, m_pos_provider, ex.get_expr());
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
            expr type = m_tc->infer(*meta);
            // first solve unassigned metavariables in type
            type = solve_unassigned_mvars(subst, type, visited);
            proof_state ps(goals(goal(*meta, type)), subst, m_ngen.mk_child());
            try_using(subst, mvar, ps, *local_hint);
        }
    }

    expr solve_unassigned_mvars(substitution & subst, expr const & e, name_set & visited) {
        buffer<expr> mvars;
        collect_metavars(e, mvars);
        for (auto mvar : mvars) {
            check_interrupted();
            solve_unassigned_mvar(subst, mvar, visited);
        }
        return subst.instantiate(e);
    }

    expr solve_unassigned_mvars(substitution & subst, expr const & e) {
        name_set visited;
        return solve_unassigned_mvars(subst, e, visited);
    }

    void display_unassigned_mvars(expr const & e, substitution const & s) {
        if (m_check_unassigned && has_metavar(e)) {
            for_each(e, [&](expr const & e, unsigned) {
                    if (!is_metavar(e))
                        return has_metavar(e);
                    if (auto it = m_mvar2meta.find(mlocal_name(e))) {
                        expr meta      = s.instantiate(*it);
                        expr meta_type = s.instantiate(type_checker(m_env).infer(meta));
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
            r = univ_metavars_to_params_fn(m_env, m_lls, s, univ_params, new_params)(r);
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

    std::tuple<expr, level_param_names> operator()(expr const & e, bool _ensure_type) {
        expr r  = visit(e);
        if (_ensure_type)
            r = ensure_type(r);
        auto p  = solve().pull();
        lean_assert(p);
        substitution s = p->first;
        return apply(s, r);
    }

    std::tuple<expr, expr, level_param_names> operator()(expr const & t, expr const & v, name const & n) {
        lean_assert(!has_local(t)); lean_assert(!has_local(v));
        expr r_t      = ensure_type(visit(t));
        expr r_v      = visit(v);
        expr r_v_type = infer_type(r_v);
        justification j = mk_justification(v, [=](formatter const & fmt, substitution const & subst) {
                return pp_def_type_mismatch(fmt, n, subst.instantiate(r_t), subst.instantiate(r_v_type));
            });
        if (!m_tc->is_def_eq(r_v_type, r_t, j)) {
            throw_kernel_exception(m_env, v, [=](formatter const & fmt) { return pp_def_type_mismatch(fmt, n, r_t, r_v_type); });
        }
        auto p  = solve().pull();
        lean_assert(p);
        substitution s = p->first;
        name_set univ_params = collect_univ_params(r_v, collect_univ_params(r_t));
        buffer<name> new_params;
        expr new_r_t = apply(s, r_t, univ_params, new_params);
        expr new_r_v = apply(s, r_v, univ_params, new_params);
        return std::make_tuple(new_r_t, new_r_v, to_list(new_params.begin(), new_params.end()));
    }
};

static name g_tmp_prefix = name::mk_internal_unique_name();

std::tuple<expr, level_param_names> elaborate(environment const & env, local_decls<level> const & lls, list<expr> const & ctx,
                                              io_state const & ios, expr const & e, pos_info_provider * pp, bool check_unassigned,
                                              bool ensure_type) {
    return elaborator(env, lls, ctx, ios, name_generator(g_tmp_prefix), pp, check_unassigned)(e, ensure_type);
}

std::tuple<expr, expr, level_param_names> elaborate(environment const & env, local_decls<level> const & lls, io_state const & ios,
                                                    name const & n, expr const & t, expr const & v, pos_info_provider * pp) {
    return elaborator(env, lls, list<expr>(), ios, name_generator(g_tmp_prefix), pp, true)(t, v, n);
}
}
