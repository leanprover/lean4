/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <vector>
#include <utility>
#include "util/pdeque.h"
#include "util/interrupt.h"
#include "kernel/formatter.h"
#include "kernel/free_vars.h"
#include "kernel/normalizer.h"
#include "kernel/instantiate.h"
#include "kernel/replace_fn.h"
#include "kernel/builtin.h"
#include "library/type_inferer.h"
#include "library/update_expr.h"
#include "library/elaborator/elaborator.h"
#include "library/elaborator/elaborator_justification.h"

namespace lean {
static name g_x_name("x");

class elaborator::imp {
    typedef pdeque<unification_constraint> cnstr_queue;

    struct state {
        metavar_env m_menv;
        cnstr_queue m_queue;

        state(metavar_env const & menv, unsigned num_cnstrs, unification_constraint const * cnstrs):
            m_menv(menv) {
            for (unsigned i = 0; i < num_cnstrs; i++)
                m_queue.push_back(cnstrs[i]);
        }

        state(metavar_env const & menv, cnstr_queue const & q):
            m_menv(menv),
            m_queue(q) {
        }
    };

    /**
       \brief Base class for case splits performed by the elaborator.
    */
    struct case_split {
        justification              m_curr_assumption; // object used to justify current split
        state                      m_prev_state;
        std::vector<justification> m_failed_justifications; // justifications for failed branches

        case_split(state const & prev_state):m_prev_state(prev_state) {}
        virtual ~case_split() {}

        virtual bool next(imp & owner) = 0;
    };

    /**
       \brief Case-split object for choice constraints.
    */
    struct choice_case_split : public case_split {
        unsigned               m_idx;
        unification_constraint m_choice;

        choice_case_split(unification_constraint const & c, state const & prev_state):
            case_split(prev_state),
            m_idx(0),
            m_choice(c) {
        }

        virtual ~choice_case_split() {}

        virtual bool next(imp & owner) {
            return owner.next_choice_case(*this);
        }
    };

    /**
       \brief General purpose case split object
    */
    struct generic_case_split : public case_split {
        unification_constraint     m_constraint;
        unsigned                   m_idx;    // current alternative
        std::vector<state>         m_states; // alternatives
        std::vector<justification> m_assumptions; // assumption for each alternative

        generic_case_split(unification_constraint const & cnstr, state const & prev_state):
            case_split(prev_state),
            m_constraint(cnstr),
            m_idx(0) {
        }

        virtual ~generic_case_split() {}

        virtual bool next(imp & owner) {
            return owner.next_generic_case(*this);
        }

        void push_back(state const & s, justification const & tr) {
            m_states.push_back(s);
            m_assumptions.push_back(tr);
        }
    };

    struct plugin_case_split : public case_split {
        unification_constraint                     m_constraint;
        std::unique_ptr<elaborator_plugin::result> m_alternatives;

        plugin_case_split(unification_constraint const & cnstr, std::unique_ptr<elaborator_plugin::result> & r, state const & prev_state):
            case_split(prev_state),
            m_constraint(cnstr),
            m_alternatives(std::move(r)) {
        }

        virtual ~plugin_case_split() {}

        virtual bool next(imp & owner) {
            return owner.next_plugin_case(*this);
        }
    };

    environment const &                      m_env;
    type_inferer                             m_type_inferer;
    normalizer                               m_normalizer;
    state                                    m_state;
    std::vector<std::unique_ptr<case_split>> m_case_splits;
    std::shared_ptr<elaborator_plugin>       m_plugin;
    unsigned                                 m_next_id;
    int                                      m_quota;
    justification                            m_conflict;
    bool                                     m_first;

    // options
    bool                                     m_use_justifications;
    bool                                     m_use_normalizer;
    bool                                     m_assume_injectivity;

    void set_options(options const &) {
        m_use_justifications = true;
        m_use_normalizer     = true;
        m_assume_injectivity = true;
    }

    void reset_quota() {
        m_quota = m_state.m_queue.size();
    }

    justification mk_assumption() {
        unsigned id = m_next_id;
        m_next_id++;
        return mk_assumption_justification(id);
    }

    /** \brief Add given constraint to the front of the current constraint queue */
    void push_front(unification_constraint const & c) {
        reset_quota();
        m_state.m_queue.push_front(c);
    }

    /** \brief Add given constraint to the end of the current constraint queue */
    void push_back(unification_constraint const & c) {
        m_state.m_queue.push_back(c);
    }

    /** \brief Return true iff \c m is an assigned metavariable in the current state */
    bool is_assigned(expr const & m) const {
        lean_assert(is_metavar(m));
        return m_state.m_menv.is_assigned(m);
    }

    /** \brief Return the substitution (and justification) for an assigned metavariable */
    std::pair<expr, justification> get_subst_jst(expr const & m) const {
        lean_assert(is_metavar(m));
        lean_assert(is_assigned(m));
        return *(m_state.m_menv.get_subst_jst(m));
    }

    /** \brief Return the type of an metavariable */
    expr get_mvar_type(expr const & m) {
        lean_assert(is_metavar(m));
        return m_state.m_menv.get_type(m);
    }

    /**
       \brief Return true iff \c e contains the metavariable \c m.
       The substitutions in the current state are taken into account.
    */
    bool has_metavar(expr const & e, expr const & m) const {
        return ::lean::has_metavar(e, m, m_state.m_menv);
    }

    static bool has_metavar(expr const & e) {
        return ::lean::has_metavar(e);
    }

    /**
       \brief Return true iff \c e contains an assigned metavariable in
       the current state.
    */
    bool has_assigned_metavar(expr const & e) const {
        return ::lean::has_assigned_metavar(e, m_state.m_menv);
    }

    /** \brief Return true if \c a is of the form <tt>(?m ...)</tt> */
    static bool is_meta_app(expr const & a) {
        return is_app(a) && is_metavar(arg(a, 0));
    }

    /** \brief Return true iff \c a is a metavariable or if \c a is an application where the function is a metavariable */
    static bool is_meta(expr const & a) {
        return is_metavar(a) || is_meta_app(a);
    }

    /** \brief Return true iff \c a is a metavariable and has a meta context. */
    static bool is_metavar_with_context(expr const & a) {
        return is_metavar(a) && has_local_context(a);
    }

    /** \brief Return true if \c a is of the form <tt>(?m[...] ...)</tt> */
    static bool is_meta_app_with_context(expr const & a) {
        return is_meta_app(a) && has_local_context(arg(a, 0));
    }

    /** \brief Return true iff \c a is a proposition */
    bool is_proposition(expr const & a, context const & ctx) {
        if ((is_metavar(a)) ||
            (is_app(a) && is_metavar(arg(a, 0))) ||
            (is_abstraction(a) && (is_metavar(abst_domain(a)) || is_metavar(abst_body(a))))) {
            // Avoid exception at m_type_inferer.
            // Throw is expensive in C++.
            return false;
        }
        try {
            return m_type_inferer.is_proposition(a, ctx);
        } catch (...) {
            return false;
        }
    }

    static expr mk_lambda(name const & n, expr const & d, expr const & b) {
        return ::lean::mk_lambda(n, d, b);
    }

    /**
       \brief Create the term (fun (x_0 : types[0]) ... (x_{n-1} : types[n-1]) body)
    */
    expr mk_lambda(buffer<expr> const & types, expr const & body) {
        expr r = body;
        unsigned i = types.size();
        while (i > 0) {
            --i;
            r = mk_lambda(i == 0 ? g_x_name : name(g_x_name, i), types[i], r);
        }
        return r;
    }

    /**
       \brief Return (f x_{num_vars - 1} ... x_0)
    */
    expr mk_app_vars(expr const & f, unsigned num_vars) {
        buffer<expr> args;
        args.push_back(f);
        unsigned i = num_vars;
        while (i > 0) {
            --i;
            args.push_back(mk_var(i));
        }
        return mk_app(args);
    }

    /**
       \brief Push a new constraint to the given constraint queue.
       If \c is_eq is true, then a equality constraint is created, otherwise a convertability constraint is created.
    */
    void push_new_constraint(cnstr_queue & q, bool is_eq, context const & new_ctx, expr const & new_a, expr const & new_b, justification const & new_jst) {
        if (is_eq)
            q.push_front(mk_eq_constraint(new_ctx, new_a, new_b, new_jst));
        else
            q.push_front(mk_convertible_constraint(new_ctx, new_a, new_b, new_jst));
    }

    /**
       \brief Push a new equality constraint <tt>new_ctx |- new_a == new_b</tt> into the given contraint queue using
       justification \c new_jst.
    */
    void push_new_eq_constraint(cnstr_queue & q, context const & new_ctx, expr const & new_a, expr const & new_b, justification const & new_jst) {
        push_new_constraint(q, true, new_ctx, new_a, new_b, new_jst);
    }

    /**
       \brief Auxiliary method for pushing a new constraint to the current constraint queue.
       If \c is_eq is true, then a equality constraint is created, otherwise a convertability constraint is created.
    */
    void push_new_constraint(bool is_eq, context const & new_ctx, expr const & new_a, expr const & new_b, justification const & new_jst) {
        reset_quota();
        push_new_constraint(m_state.m_queue, is_eq, new_ctx, new_a, new_b, new_jst);
    }

    /**
       \brief Auxiliary method for pushing a new constraint to the current constraint queue.
       The new constraint is based on the constraint \c c. The constraint \c c may be a equality or convertability constraint.
       The update is justified by \c new_jst.
    */
    void push_updated_constraint(unification_constraint const & c, expr const & new_a, expr const & new_b, justification const & new_jst) {
        lean_assert(is_eq(c) || is_convertible(c));
        context const & ctx = get_context(c);
        if (is_eq(c))
            push_front(mk_eq_constraint(ctx, new_a, new_b, new_jst));
        else
            push_front(mk_convertible_constraint(ctx, new_a, new_b, new_jst));
    }

    /**
       \brief Auxiliary method for pushing a new constraint to the current constraint queue.
       The new constraint is based on the constraint \c c. The constraint \c c may be a equality or convertability constraint.
       The flag \c is_lhs says if the left-hand-side or right-hand-side are being updated with \c new_a.
       The update is justified by \c new_jst.
    */
    void push_updated_constraint(unification_constraint const & c, bool is_lhs, expr const & new_a, justification const & new_jst) {
        lean_assert(is_eq(c) || is_convertible(c));
        context const & ctx = get_context(c);
        if (is_eq(c)) {
            if (is_lhs)
                push_front(mk_eq_constraint(ctx, new_a, eq_rhs(c), new_jst));
            else
                push_front(mk_eq_constraint(ctx, eq_lhs(c), new_a, new_jst));
        } else {
            if (is_lhs)
                push_front(mk_convertible_constraint(ctx, new_a, convertible_to(c), new_jst));
            else
                push_front(mk_convertible_constraint(ctx, convertible_from(c), new_a, new_jst));
        }
    }

    /**
       \brief Auxiliary method for pushing a new constraint to the constraint queue.
       The new constraint is obtained from \c c by one or more normalization steps that produce \c new_a and \c new_b
    */
    void push_normalized_constraint(unification_constraint const & c, expr const & new_a, expr const & new_b) {
        push_updated_constraint(c, new_a, new_b, justification(new normalize_justification(c)));
    }

    /**
       \brief Assign \c v to \c m with justification \c tr in the current state.
    */
    void assign(expr const & m, expr const & v, unification_constraint const & c) {
        lean_assert(is_metavar(m));
        reset_quota();
        context const & ctx = get_context(c);
        justification jst(new assignment_justification(c));
        metavar_env & menv = m_state.m_menv;
        m_state.m_menv.assign(m, v, jst);
        if (menv.has_type(m)) {
            buffer<unification_constraint> ucs;
            expr tv = m_type_inferer(v, ctx, &menv, &ucs);
            for (auto c : ucs)
                push_front(c);
            justification new_jst(new typeof_mvar_justification(ctx, m, menv.get_type(m), tv, jst));
            push_front(mk_convertible_constraint(ctx, tv, menv.get_type(m), new_jst));
        }
    }

    bool process(unification_constraint const & c) {
        m_quota--;
        switch (c.kind()) {
        case unification_constraint_kind::Eq:          return process_eq(c);
        case unification_constraint_kind::Convertible: return process_convertible(c);
        case unification_constraint_kind::Max:         return process_max(c);
        case unification_constraint_kind::Choice:      return process_choice(c);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
        return true;
    }

    bool process_eq(unification_constraint const & c) {
        return process_eq_convertible(get_context(c), eq_lhs(c), eq_rhs(c), c);
    }

    bool process_convertible(unification_constraint const & c) {
        return process_eq_convertible(get_context(c), convertible_from(c), convertible_to(c), c);
    }

    /**
       Process <tt>ctx |- a == b</tt> and <tt>ctx |- a << b</tt> when:
       1- \c a is an assigned metavariable
       2- \c a is a unassigned metavariable without a metavariable context.
       3- \c a is a unassigned metavariable of the form <tt>?m[lift:s:n, ...]</tt>, and \c b does not have
          a free variable in the range <tt>[s, s+n)</tt>.
       4- \c a is an application of the form <tt>(?m ...)</tt> where ?m is an assigned metavariable.
    */
    enum status { Processed, Failed, Continue };
    status process_metavar(unification_constraint const & c, expr const & a, expr const & b, bool is_lhs) {
        context const & ctx = get_context(c);
        if (is_metavar(a)) {
            if (is_assigned(a)) {
                // Case 1
                auto s_j = get_subst_jst(a);
                justification new_jst(new substitution_justification(c, s_j.second));
                push_updated_constraint(c, is_lhs, s_j.first, new_jst);
                return Processed;
            } else if (!has_local_context(a)) {
                // Case 2
                if (has_metavar(b, a)) {
                    m_conflict = justification(new unification_failure_justification(c));
                    return Failed;
                } else if (is_eq(c) || is_proposition(b, ctx)) {
                    // At this point, we only assign metavariables if the constraint is an equational constraint,
                    // or b is a proposition.
                    // It is important to handle propositions since we don't want to normalize them.
                    // The normalization process destroys the structure of the proposition.
                    assign(a, b, c);
                    return Processed;
                }
            } else {
                local_entry const & me = head(metavar_lctx(a));
                if (me.is_lift()) {
                    if (!has_free_var(b, me.s(), me.s() + me.n(), m_state.m_menv)) {
                        // Case 3
                        justification new_jst(new normalize_justification(c));
                        expr new_a = pop_meta_context(a);
                        expr new_b = lower_free_vars(b, me.s() + me.n(), me.n(), m_state.m_menv);
                        context new_ctx = ctx.remove(me.s(), me.n());
                        if (!is_lhs)
                            swap(new_a, new_b);
                        push_new_constraint(is_eq(c), new_ctx, new_a, new_b, new_jst);
                        return Processed;
                    } else if (is_var(b)) {
                        // Failure, there is no way to unify
                        // ?m[lift:s:n, ...] with a variable in [s, s+n]
                        m_conflict = justification(new unification_failure_justification(c));
                        return Failed;
                    }
                } else if (me.is_inst() && is_proposition(b, ctx) && !is_proposition(me.v(), ctx)) {
                    // If b is a proposition, and the value in the local context is not,
                    // we ignore it, and create new constraint without the head of the local context.
                    // This is a little bit hackish. We do it because we want to preserve
                    // the structure of the proposition. This is similar to the trick used
                    // in the assign(a, b, c) branch above.
                    justification new_jst(new normalize_justification(c));
                    expr new_a = pop_meta_context(a);
                    expr new_b = lift_free_vars(b, me.s(), 1);
                    context new_ctx = ctx.insert_at(me.s(), g_x_name, Type()); // insert a dummy at position s
                    if (!is_lhs)
                        swap(new_a, new_b);
                    push_new_constraint(is_eq(c), new_ctx, new_a, new_b, new_jst);
                    return Processed;
                }
            }
        }

        if (is_app(a) && is_metavar(arg(a, 0)) && is_assigned(arg(a, 0))) {
            // Case 4
            auto s_j = get_subst_jst(arg(a, 0));
            justification new_jst(new substitution_justification(c, s_j.second));
            expr new_f = s_j.first;
            expr new_a = update_app(a, 0, new_f);
            if (m_state.m_menv.beta_reduce_metavar_application())
                new_a = head_beta_reduce(new_a);
            push_updated_constraint(c, is_lhs, new_a, new_jst);
            return Processed;
        }
        return Continue;
    }

    justification mk_subst_justification(unification_constraint const & c, buffer<justification> const & subst_justifications) {
        if (subst_justifications.size() == 1) {
            return justification(new substitution_justification(c, subst_justifications[0]));
        } else {
            return justification(new multi_substitution_justification(c, subst_justifications.size(), subst_justifications.data()));
        }
    }

    /**
       \brief Instantiate the assigned metavariables in \c a, and store the justifications
       in \c jsts.
    */
    expr instantiate_metavars(expr const & a, buffer<justification> & jsts) {
        lean_assert(has_assigned_metavar(a));
        return ::lean::instantiate_metavars(a, m_state.m_menv, jsts);
    }

    /**
       \brief Return true iff \c a contains instantiated variables. If this is the case,
       then constraint \c c is updated with a new \c a s.t. all metavariables of \c a
       are instantiated.

       \remark if \c is_lhs is true, then we are considering the left-hand-side of the constraint \c c.
    */
    bool instantiate_metavars(bool is_lhs, expr const & a, unification_constraint const & c) {
        lean_assert(is_eq(c) || is_convertible(c));
        lean_assert(!is_eq(c) || !is_lhs || is_eqp(eq_lhs(c), a));
        lean_assert(!is_eq(c) ||  is_lhs || is_eqp(eq_rhs(c), a));
        lean_assert(!is_convertible(c) || !is_lhs || is_eqp(convertible_from(c), a));
        lean_assert(!is_convertible(c) ||  is_lhs || is_eqp(convertible_to(c), a));
        if (has_assigned_metavar(a)) {
            buffer<justification> jsts;
            expr new_a = instantiate_metavars(a, jsts);
            justification new_jst = mk_subst_justification(c, jsts);
            push_updated_constraint(c, is_lhs, new_a, new_jst);
            return true;
        } else {
            return false;
        }
    }

    /** \brief Unfold let-expression */
    void process_let(expr & a) {
        if (is_let(a))
            a = instantiate(let_body(a), let_value(a));
    }

    /** \brief Replace variables by their definition if the context contains it. */
    void process_var(context const & ctx, expr & a) {
        if (is_var(a)) {
            auto e = find(ctx, var_idx(a));
            if (e && e->get_body())
                a = *(e->get_body());
        }
    }

    expr normalize(context const & ctx, expr const & a) {
        return m_normalizer(a, ctx);
    }

    void process_app(context const & ctx, expr & a) {
        if (is_app(a)) {
            expr f = arg(a, 0);
            if (is_value(f) && m_use_normalizer) {
                // if f is a semantic attachment, we keep normalizing children from
                // left to right until the semantic attachment is applicable
                buffer<expr> new_args;
                new_args.append(num_args(a), &(arg(a, 0)));
                bool modified = false;
                expr r;
                for (unsigned i = 1; i < new_args.size(); i++) {
                    expr const & curr = new_args[i];
                    expr new_curr = normalize(ctx, curr);
                    if (curr != new_curr) {
                        modified = true;
                        new_args[i] = new_curr;
                        if (optional<expr> r = to_value(f).normalize(new_args.size(), new_args.data())) {
                            a = *r;
                            return;
                        }
                    }
                }
                if (optional<expr> r = to_value(f).normalize(new_args.size(), new_args.data())) {
                    a = *r;
                    return;
                }
                if (modified) {
                    a = mk_app(new_args);
                    return;
                }
            } else {
                process_let(f);
                process_var(ctx, f);
                f = head_beta_reduce(f);
                a = update_app(a, 0, f);
                a = head_beta_reduce(a);
            }
        }
    }

    void process_eq(context const & ctx, expr & a) {
        if (is_eq(a) && m_use_normalizer) {
            a = normalize(ctx, a);
        }
    }

    expr normalize_step(context const & ctx, expr const & a) {
        expr new_a = a;
        process_let(new_a);
        process_var(ctx, new_a);
        process_app(ctx, new_a);
        process_eq(ctx, new_a);
        return new_a;
    }

    int get_const_weight(expr const & a) {
        lean_assert(is_constant(a));
        optional<object> obj = m_env.find_object(const_name(a));
        if (obj && obj->is_definition() && !obj->is_opaque())
            return obj->get_weight();
        else
            return -1;
    }

    /**
        \brief Return a number >= 0 if \c a is a defined constant or the application of a defined constant.
        In this case, the value is the weight of the definition.
    */
    int get_unfolding_weight(expr const & a) {
        if (is_constant(a))
            return get_const_weight(a);
        else if (is_app(a) && is_constant(arg(a, 0)))
            return get_const_weight(arg(a, 0));
        else
            return -1;
    }

    expr unfold(expr const & a) {
        lean_assert(is_constant(a) || (is_app(a) && is_constant(arg(a, 0))));
        if (is_constant(a)) {
            lean_assert(m_env.find_object(const_name(a)));
            return m_env.find_object(const_name(a))->get_value();
        } else {
            lean_assert(m_env.find_object(const_name(arg(a, 0))));
            return update_app(a, 0, m_env.find_object(const_name(arg(a, 0)))->get_value());
        }
    }

    bool normalize_head(expr a, expr b, unification_constraint const & c) {
        context const & ctx = get_context(c);
        bool modified = false;
        while (true) {
            check_interrupted();
            expr new_a = normalize_step(ctx, a);
            expr new_b = normalize_step(ctx, b);
            if (new_a == a && new_b == b) {
                int w_a = get_unfolding_weight(a);
                int w_b = get_unfolding_weight(b);
                if (w_a >= 0 || w_b >= 0) {
                    if (w_a >= w_b)
                        new_a = unfold(a);
                    if (w_b >= w_a)
                        new_b = unfold(b);
                    if (new_a == a && new_b == b)
                        break;
                } else {
                    break;
                }
            }
            modified = true;
            a = new_a;
            b = new_b;
            if (a == b) {
                return true;
            }
        }
        if (modified) {
            push_normalized_constraint(c, a, b);
            return true;
        } else {
            return false;
        }
    }

    /** \brief Return true iff the variable with id \c vidx has a body/definition in the context \c ctx. */
    static bool has_body(context const & ctx, unsigned vidx) {
        auto e = find(ctx, vidx);
        return e && e->get_body();
    }

    /**
       \brief Return true iff all arguments of the application \c a are variables that do
       not have a definition in \c ctx.
    */
    static bool are_args_vars(context const & ctx, expr const & a) {
        lean_assert(is_app(a));
        for (unsigned i = 1; i < num_args(a); i++) {
            if (!is_var(arg(a, i)))
                return false;
            if (has_body(ctx, var_idx(arg(a, i))))
                return false;
        }
        return true;
    }

    /**
       \brief Return true iff \c a may be an actual lower bound for a convertibility constraint.
       That is, if the result is false, it means the convertability constraint is essentially
       an equality constraint.
    */
    bool is_actual_lower(expr const & a) {
        return is_type(a) || is_metavar(a) || is_bool(a) || (is_pi(a) && is_actual_lower(abst_body(a)));
    }

    /**
       \brief Return true iff \c a may be an actual upper bound for a convertibility constraint.
       That is, if the result is false, it means the convertability constraint is essentially
       an equality constraint.
    */
    bool is_actual_upper(expr const & a) {
        return is_type(a) || is_metavar(a) || (is_pi(a) && is_actual_upper(abst_body(a)));
    }

    /**
       \brief See \c process_simple_ho_match
    */
    bool is_simple_ho_match(context const & ctx, expr const & a, expr const & b, bool is_lhs, unification_constraint const & c) {
        return is_meta_app(a) && are_args_vars(ctx, a) && closed(b) &&
            (is_eq(c) || (is_lhs && !is_actual_upper(b)) || (!is_lhs && !is_actual_lower(b)));
    }

    /**
        \brief Return true iff ctx |- a == b is a "simple" higher-order matching constraint. By simple, we mean
        a constraint of the form
               ctx |- (?m x) == c
        The constraint is solved by assigning ?m to (fun (x : T), c).
    */
    bool process_simple_ho_match(context const & ctx, expr const & a, expr const & b, bool is_lhs, unification_constraint const & c) {
        // Solve constraint of the form
        //    ctx |- (?m x) == c
        // using imitation
        if (is_simple_ho_match(ctx, a, b, is_lhs, c)) {
            expr m = arg(a, 0);
            buffer<expr> types;
            for (unsigned i = 1; i < num_args(a); i++) {
                optional<expr> d = lookup(ctx, var_idx(arg(a, i))).get_domain();
                if (d)
                    types.push_back(*d);
                else
                    return false;
            }
            justification new_jst(new destruct_justification(c));
            expr s = mk_lambda(types, b);
            if (!is_lhs)
                swap(m, s);
            push_front(mk_eq_constraint(ctx, m, s, new_jst));
            return true;
        } else {
            return false;
        }
    }

    /**
       \brief Auxiliary method for \c process_meta_app. Add new case-splits to new_cs
    */
    void process_meta_app_core(std::unique_ptr<generic_case_split> & new_cs, expr const & a, expr const & b, bool is_lhs, unification_constraint const & c) {
        lean_assert(is_meta_app(a));
        context const & ctx = get_context(c);
        metavar_env & menv  = m_state.m_menv;
        expr f_a            = arg(a, 0);
        lean_assert(is_metavar(f_a));
        unsigned num_a      = num_args(a);
        buffer<expr> arg_types;
        buffer<unification_constraint> ucs;
        context h_ctx = ctx;  // context for new fresh metavariables used in the imitation step
        for (unsigned i = 1; i < num_a; i++) {
            arg_types.push_back(m_type_inferer(arg(a, i), ctx, &menv, &ucs));
            for (auto uc : ucs)
                push_front(uc);
            h_ctx = extend(h_ctx, name(g_x_name, i), arg_types.back());
        }
        // Add projections
        for (unsigned i = 1; i < num_a; i++) {
            // Assign f_a <- fun (x_1 : T_0) ... (x_{num_a-1} : T_{num_a-1}), x_i
            state new_state(m_state);
            justification new_assumption = mk_assumption();
            expr proj            = mk_lambda(arg_types, mk_var(num_a - i - 1));
            expr new_a           = arg(a, i);
            expr new_b           = b;
            if (!is_lhs)
                swap(new_a, new_b);
            push_new_constraint(new_state.m_queue, is_eq(c), ctx, new_a, new_b, new_assumption);
            push_new_eq_constraint(new_state.m_queue, ctx, f_a, proj, new_assumption);
            new_cs->push_back(new_state, new_assumption);
        }
        // Add imitation
        state new_state(m_state);
        justification new_assumption = mk_assumption();
        expr imitation;
        lean_assert(arg_types.size() == num_a - 1);
        if (is_app(b)) {
            // Imitation for applications
            expr f_b          = arg(b, 0);
            unsigned num_b    = num_args(b);
            // Assign f_a <- fun (x_1 : T_1) ... (x_{num_a} : T_{num_a}), f_b (h_1 x_1 ... x_{num_a}) ... (h_{num_b} x_1 ... x_{num_a})
            // New constraints (h_i a_1 ... a_{num_a}) == arg(b, i)
            buffer<expr> imitation_args; // arguments for the imitation
            imitation_args.push_back(lift_free_vars(f_b, 0, num_a - 1));
            for (unsigned i = 1; i < num_b; i++) {
                // Remark: h_ctx is "ctx, (x_{num_a} : T_{num_a}) ... (x_1 : T_1)" because h_i is inside of the lambda
                expr h_i = new_state.m_menv.mk_metavar(h_ctx);
                imitation_args.push_back(mk_app_vars(h_i, num_a - 1));
                push_new_eq_constraint(new_state.m_queue, ctx, update_app(a, 0, h_i), arg(b, i), new_assumption);
            }
            imitation = mk_lambda(arg_types, mk_app(imitation_args));
        } else if (is_eq(b)) {
            // Imitation for equality
            // Assign f_a <- fun (x_1 : T_1) ... (x_{num_a} : T_{num_a}), (h_1 x_1 ... x_{num_a}) = (h_2 x_1 ... x_{num_a})
            // New constraints (h_1 a_1 ... a_{num_a}) == eq_lhs(b)
            //                 (h_2 a_1 ... a_{num_a}) == eq_rhs(b)
            expr h_1 = new_state.m_menv.mk_metavar(h_ctx);
            expr h_2 = new_state.m_menv.mk_metavar(h_ctx);
            push_new_eq_constraint(new_state.m_queue, ctx, update_app(a, 0, h_1), eq_lhs(b), new_assumption);
            push_new_eq_constraint(new_state.m_queue, ctx, update_app(a, 0, h_2), eq_rhs(b), new_assumption);
            imitation = mk_lambda(arg_types, mk_eq(mk_app_vars(h_1, num_a - 1), mk_app_vars(h_2, num_a - 1)));
        } else if (is_abstraction(b)) {
            // Imitation for lambdas and Pis
            // Assign f_a <- fun (x_1 : T_1) ... (x_{num_a} : T_{num_a}),
            //                        fun (x_b : (?h_1 x_1 ... x_{num_a})), (?h_2 x_1 ... x_{num_a} x_b)
            // New constraints (h_1 a_1 ... a_{num_a}) == abst_domain(b)
            //                 (h_2 a_1 ... a_{num_a} x_b) == abst_body(b)
            expr h_1 = new_state.m_menv.mk_metavar(h_ctx);
            context new_ctx = extend(ctx, abst_name(b), abst_domain(b));
            expr h_2 = new_state.m_menv.mk_metavar(extend(h_ctx, abst_name(b), abst_domain(b)));
            push_new_eq_constraint(new_state.m_queue, ctx, update_app(a, 0, h_1), abst_domain(b), new_assumption);
            push_new_eq_constraint(new_state.m_queue, new_ctx,
                                   mk_app(update_app(a, 0, h_2), mk_var(0)), abst_body(b), new_assumption);
            imitation = mk_lambda(arg_types, update_abstraction(b, mk_app_vars(h_1, num_a - 1), mk_app_vars(h_2, num_a)));
        } else {
            // "Dumb imitation" aka the constant function
            // Assign f_a <- fun (x_1 : T_1) ... (x_{num_a} : T_{num_a}), b
            imitation = mk_lambda(arg_types, lift_free_vars(b, 0, num_a - 1));
        }
        push_new_eq_constraint(new_state.m_queue, ctx, f_a, imitation, new_assumption);
        new_cs->push_back(new_state, new_assumption);
    }

    /**
       \brief Process a constraint <tt>ctx |- a = b</tt> where \c a is of the form <tt>(?m ...)</tt>.
       We perform a "case split" using "projection" or "imitation". See Huet&Lang's paper on higher order matching
       for further details.
    */
    bool process_meta_app(expr const & a, expr const & b, bool is_lhs, unification_constraint const & c, bool flex_flex = false) {
        if (is_meta_app(a) && (flex_flex || !is_meta_app(b))) {
            std::unique_ptr<generic_case_split> new_cs(new generic_case_split(c, m_state));
            process_meta_app_core(new_cs, a, b, is_lhs, c);
            if (flex_flex && is_meta_app(b))
                process_meta_app_core(new_cs, b, a, !is_lhs, c);
            bool r = new_cs->next(*this);
            lean_assert(r);
            m_case_splits.push_back(std::move(new_cs));
            reset_quota();
            return r;
        } else {
            return false;
        }
    }

    /** \brief Return true if \c a is of the form ?m[inst:i t, ...] */
    bool is_metavar_inst(expr const & a) const {
        return is_metavar(a) && has_local_context(a) && head(metavar_lctx(a)).is_inst();
    }

    /** \brief Return true if \c a is of the form ?m[lift:s:n, ...] */
    bool is_metavar_lift(expr const & a) const {
        return is_metavar(a) && has_local_context(a) && head(metavar_lctx(a)).is_lift();
    }

    /**
       \brief A neutral abstraction is an Arrow (if the abstraction is a Pi) or a constant function (if the abstraction is a lambda).
    */
    bool is_neutral_abstraction(expr const & a, metavar_env const & menv) {
        return is_abstraction(a) && !has_free_var(abst_body(a), 0, menv);
    }
    bool is_neutral_abstraction(expr const & a) {
        return is_neutral_abstraction(a, m_state.m_menv);
    }


    /**
       \brief Process a constraint <tt>ctx |- a == b</tt> where \c a is of the form <tt>?m[(inst:i t), ...]</tt>.
       We perform a "case split",
       Case 1) ?m[...] == #i and t == b
       Case 2) imitate b
    */
    bool process_metavar_inst(expr const & a, expr const & b, bool is_lhs, unification_constraint const & c) {
        if (is_metavar_inst(a) && !is_metavar_inst(b) && !is_meta_app(b)) {
            // Remark: the condition !is_abstraction(b) || is_neutral_abstraction(b)
            // is used to make sure we don't enter a loop.
            // This is just a conservative step to make sure the elaborator does diverge.
            context const & ctx = get_context(c);
            local_context  lctx = metavar_lctx(a);
            unsigned i          = head(lctx).s();
            expr t              = head(lctx).v();

            metavar_env & menv  = m_state.m_menv;
            buffer<unification_constraint> ucs;
            expr b_type = m_type_inferer(b, ctx, &menv, &ucs);
            for (auto uc : ucs)
                m_state.m_queue.push_front(uc);
            context ctx_with_i = ctx.insert_at(i, g_x_name, b_type); // must add entry for variable #i in the context

            std::unique_ptr<generic_case_split> new_cs(new generic_case_split(c, m_state));
            {
                // Case 1
                state new_state(m_state);
                justification new_assumption = mk_assumption();
                // add ?m[...] == #1
                push_new_eq_constraint(new_state.m_queue, ctx_with_i, pop_meta_context(a), mk_var(i), new_assumption);
                // add t == b (t << b)
                expr new_a = t;
                expr new_b = b;
                if (!is_lhs)
                    swap(new_a, new_b);
                push_new_constraint(new_state.m_queue, is_eq(c), ctx, new_a, new_b, new_assumption);
                new_cs->push_back(new_state, new_assumption);
            }
            {
                // Case 2
                state new_state(m_state);
                justification new_assumption = mk_assumption();
                expr  imitation;
                if (is_app(b)) {
                    // Imitation for applications b == f(s_1, ..., s_k)
                    // mname <- f(?h_1, ..., ?h_k)
                    expr f_b          = arg(b, 0);
                    unsigned num_b    = num_args(b);
                    buffer<expr> imitation_args;
                    imitation_args.push_back(f_b);
                    for (unsigned i = 1; i < num_b; i++) {
                        expr h_i = new_state.m_menv.mk_metavar(ctx);
                        imitation_args.push_back(h_i);
                    }
                    imitation = mk_app(imitation_args);
                } else if (is_eq(b)) {
                    // Imitation for equality b == Eq(s1, s2)
                    // mname <- Eq(?h_1, ?h_2)
                    expr h_1 = new_state.m_menv.mk_metavar(ctx);
                    expr h_2 = new_state.m_menv.mk_metavar(ctx);
                    imitation = mk_eq(h_1, h_2);
                } else if (is_abstraction(b)) {
                    // Lambdas and Pis
                    // Imitation for Lambdas and Pis, b == Fun(x:T) B
                    // mname <- Fun (x:?h_1) ?h_2
                    // Remark: we don't need to use (Fun (x:?h_1) (?h_2 x)) because when b
                    // is a neutral abstraction (arrow or constant function).
                    // We avoid the more general (Fun (x:?h_1) (?h_2 x)) because it produces
                    // non-termination.
                    expr h_1 = new_state.m_menv.mk_metavar(ctx);
                    context new_ctx = extend(ctx, abst_name(b), abst_domain(b));
                    expr h_2 = new_state.m_menv.mk_metavar(new_ctx);
                    if (is_neutral_abstraction(b, new_state.m_menv))
                        imitation = update_abstraction(b, h_1, h_2);
                    else
                        imitation = update_abstraction(b, h_1, mk_app(h_2, Var(0)));
                } else {
                    imitation = lift_free_vars(b, i, 1);
                }
                new_state.m_queue.push_front(c); // keep c
                push_new_eq_constraint(new_state.m_queue, ctx_with_i, mk_metavar(metavar_name(a)), imitation, new_assumption);
                new_cs->push_back(new_state, new_assumption);
            }
            bool r = new_cs->next(*this);
            lean_assert(r);
            m_case_splits.push_back(std::move(new_cs));
            reset_quota();
            return r;
        } else {
            return false;
        }
    }

    /**
       \brief Process a constraint of the form <tt>ctx |- ?m[lift, ...] == b</tt> where \c b is an abstraction.
       That is, \c b is a Pi or Lambda. In both cases, ?m must have the same kind.
       We just add a new assignment that forces ?m to have the corresponding kind.
    */
    bool process_metavar_lift_abstraction(expr const & a, expr const & b, unification_constraint const & c) {
        if (is_metavar_lift(a) && is_abstraction(b) && is_neutral_abstraction(b)) {
            push_back(c);
            context const & ctx = get_context(c);
            expr h_1 = m_state.m_menv.mk_metavar(ctx);
            expr h_2 = m_state.m_menv.mk_metavar(ctx);
            // We don't use h_2(Var 0) in the body of the imitation term because
            // b is a neutral abstraction (arrow or constant function).
            // See comment at process_metavar_inst
            expr imitation = update_abstraction(b, h_1, h_2);
            expr ma  = mk_metavar(metavar_name(a));
            justification new_jst(new imitation_justification(c));
            push_new_constraint(true, ctx, ma, imitation, new_jst);
            return true;
        } else {
            return false;
        }
    }

    /**
       \brief Return true iff c is a constraint of the form <tt>ctx |- a << ?m</tt>, where \c a is Type or Bool
     */
    bool is_lower(unification_constraint const & c) {
        return
            is_convertible(c) &&
            is_metavar(convertible_to(c)) &&
            (is_bool(convertible_from(c)) || is_type(convertible_from(c)));
    }

    /** \brief Process constraint of the form <tt>ctx |- a << ?m</tt>, where \c a is Type or Bool */
    bool process_lower(expr const & a, expr const & b, unification_constraint const & c) {
        if (is_lower(c)) {
            // Remark: in principle, there are infinite number of choices.
            // We approximate and only consider the most useful ones.
            justification new_jst(new destruct_justification(c));
            if (is_bool(a)) {
                expr choices[5] = { Bool, Type(), Type(level() + 1), TypeM, TypeU };
                push_front(mk_choice_constraint(get_context(c), b, 5, choices, new_jst));
                return true;
            } else {
                expr choices[5] = { a, Type(ty_level(a) + 1), Type(ty_level(a) + 2), TypeM, TypeU };
                push_front(mk_choice_constraint(get_context(c), b, 5, choices, new_jst));
                return true;
            }
        } else {
            return false;
        }
    }

    /**
       \brief Return true if the current queue contains a constraint that satisfies the predicate p
    */
    template<typename P>
    bool has_constraint(P p) {
        auto it  = m_state.m_queue.begin();
        auto end = m_state.m_queue.end();
        for (; it != end; ++it) {
            unification_constraint const & c = *it;
            if (p(c))
                return true;
        }
        return false;
    }

    /**
       \brief Return true iff the current queue has a max constraint of the form <tt>ctx |- max(L1, L2) == a</tt>.

       \pre is_metavar(a)
    */
    bool has_max_constraint(expr const & a) {
        lean_assert(is_metavar(a));
        return has_constraint([&](unification_constraint const & c) { return is_max(c) && max_rhs(c) == a; });
    }


    /**
       \brief Return true iff the current queue has a constraint that is a lower bound for \c a.
       \pre is_metavar(a)
    */
    bool has_lower(expr const & a) {
        lean_assert(is_metavar(a));
        return has_constraint([&](unification_constraint const & c) { return is_lower(c) && convertible_to(c) == a; });
    }

    /** \brief Process constraint of the form <tt>ctx |- ?m << b</tt>, where \c a is Type */
    bool process_upper(expr const & a, expr const & b, unification_constraint const & c) {
        if (is_convertible(c) && is_metavar(a) && is_type(b) && !has_max_constraint(a) && !has_lower(a)) {
            // Remark: in principle, there are infinite number of choices.
            // We approximate and only consider the most useful ones.
            //
            // Remark: we only consider \c a if the queue does not have a constraint
            // of the form ctx |- max(L1, L2) == a.
            // If it does, we don't need to guess. We wait \c a to be assigned
            // and just check if the upper bound is satisfied.
            //
            // Remark: we also give preference to lower bounds
            justification new_jst(new destruct_justification(c));
            if (b == Type()) {
                expr choices[2] = { Type(), Bool };
                push_front(mk_choice_constraint(get_context(c), a, 2, choices, new_jst));
                return true;
            } else if (b == TypeU) {
                expr choices[5] = { TypeU, TypeM, Type(level() + 1), Type(), Bool };
                push_front(mk_choice_constraint(get_context(c), a, 5, choices, new_jst));
                return true;
            } else if (b == TypeM) {
                expr choices[4] = { TypeM, Type(level() + 1), Type(), Bool };
                push_front(mk_choice_constraint(get_context(c), a, 4, choices, new_jst));
                return true;
            } else {
                level const & lvl = ty_level(b);
                lean_assert(!lvl.is_bottom());
                if (is_lift(lvl)) {
                    // If  b is (Type L + k)
                    // make choices == { Type(L + k), Type(L + k - 1), ..., Type(L), Type, Bool }
                    buffer<expr> choices;
                    unsigned k = lift_offset(lvl);
                    level L = lift_of(lvl);
                    lean_assert(k > 0);
                    while (k > 0) {
                        choices.push_back(mk_type(L + k));
                        k--;
                    }
                    choices.push_back(mk_type(L));
                    if (!L.is_bottom())
                        choices.push_back(Type());
                    choices.push_back(Bool);
                    push_front(mk_choice_constraint(get_context(c), a, choices.size(), choices.data(), new_jst));
                    return true;
                } else if (is_uvar(lvl)) {
                    expr choices[4] = { Type(level() + 1), Type(), b, Bool };
                    push_front(mk_choice_constraint(get_context(c), a, 4, choices, new_jst));
                    return true;
                } else {
                    lean_assert(is_max(lvl));
                    // TODO(Leo)
                    return false;
                }
            }
        } else {
            return false;
        }
    }

    bool process_eq_convertible(context const & ctx, expr const & a, expr const & b, unification_constraint const & c) {
        bool eq = is_eq(c);
        if (a == b) {
            return true;
        }

        if (m_assume_injectivity && is_app(a) && is_app(b) && num_args(a) == num_args(b) && arg(a, 0) == arg(b, 0)) {
            // If m_assume_injectivity is true, we apply the following rule
            // ctx |- (f a1 a2) == (f b1 b2)
            // ===>
            // ctx |- a1 == b1
            // ctx |- a2 == b2
            justification new_jst(new destruct_justification(c));
            for (unsigned i = 1; i < num_args(a); i++)
                push_front(mk_eq_constraint(ctx, arg(a, i), arg(b, i), new_jst));
            return true;
        }

        status r;
        r = process_metavar(c, a, b, true);
        if (r != Continue) { return r == Processed; }
        r = process_metavar(c, b, a, false);
        if (r != Continue) { return r == Processed; }

        if (normalize_head(a, b, c)) { return true; }

        if (!eq) {
            // TODO(Leo): use is_actual_lower and is_actual_upper

            // Try to assign convertability constraints.
            if (!is_type(b) && !is_meta(b) && is_metavar(a) && !is_assigned(a) && !has_local_context(a)) {
                // We can assign a <- b at this point IF b is not (Type lvl) or Metavariable
                lean_assert(!has_metavar(b, a));
                assign(a, b, c);
                return true;
            }
            if (!is_type(a) && !is_meta(a) && a != Bool && is_metavar(b) && !is_assigned(b) && !has_local_context(b)) {
                // We can assign b <- a at this point IF a is not (Type lvl) or Metavariable or Bool.
                lean_assert(!has_metavar(a, b));
                assign(b, a, c);
                return true;
            }
        }

        // TODO(Leo): normalize pi domain... to make sure we are not missing solutions in process_simple_ho_match

        if (process_simple_ho_match(ctx, a, b, true, c) ||
            process_simple_ho_match(ctx, b, a, false, c))
            return true;

        if (!eq && is_bool(a) && is_type(b))
            return true;

        if (a.kind() == b.kind()) {
            switch (a.kind()) {
            case expr_kind::Constant: case expr_kind::Var: case expr_kind::Value:
                if (a == b) {
                    return true;
                } else {
                    m_conflict = justification(new unification_failure_justification(c));
                    return false;
                }
            case expr_kind::Type:
                if ((!eq && m_env.is_ge(ty_level(b), ty_level(a))) || (eq && a == b)) {
                    return true;
                } else {
                    m_conflict = justification(new unification_failure_justification(c));
                    return false;
                }
            case expr_kind::Eq: {
                justification new_jst(new destruct_justification(c));
                push_front(mk_eq_constraint(ctx, eq_lhs(a), eq_lhs(b), new_jst));
                push_front(mk_eq_constraint(ctx, eq_rhs(a), eq_rhs(b), new_jst));
                return true;
            }
            case expr_kind::Pi: {
                justification new_jst(new destruct_justification(c));
                push_front(mk_eq_constraint(ctx, abst_domain(a), abst_domain(b), new_jst));
                context new_ctx = extend(ctx, abst_name(a), abst_domain(a));
                if (eq)
                    push_front(mk_eq_constraint(new_ctx, abst_body(a), abst_body(b), new_jst));
                else
                    push_front(mk_convertible_constraint(new_ctx, abst_body(a), abst_body(b), new_jst));
                return true;
            }
            case expr_kind::Lambda: {
                justification new_jst(new destruct_justification(c));
                push_front(mk_eq_constraint(ctx, abst_domain(a), abst_domain(b), new_jst));
                context new_ctx = extend(ctx, abst_name(a), abst_domain(a));
                push_front(mk_eq_constraint(new_ctx, abst_body(a), abst_body(b), new_jst));
                return true;
            }
            case expr_kind::App:
                if (!is_meta_app(a) && !is_meta_app(b)) {
                    if (num_args(a) == num_args(b)) {
                        justification new_jst(new destruct_justification(c));
                        for (unsigned i = 0; i < num_args(a); i++)
                            push_front(mk_eq_constraint(ctx, arg(a, i), arg(b, i), new_jst));
                        return true;
                    } else {
                        m_conflict = justification(new unification_failure_justification(c));
                        return false;
                    }
                }
                break;
            case expr_kind::Let:
                lean_unreachable(); // LCOV_EXCL_LINE
                return true;
            default:
                break;
            }
        }

        if (instantiate_metavars(true, a, c) ||
            instantiate_metavars(false, b, c)) {
            return true;
        }

        // If 'a' and 'b' have different kinds, and 'a' and 'b' are not metavariables,
        // and 'a' and 'b' are not applications where the function contains metavariables,
        // then it is not possible to unify 'a' and 'b'.
        // We need the last condition because if 'a'/'b' are applications containing metavariables,
        // then they can be reduced when the metavariable is assigned
        // Here is an example:
        //     |- (?m Type) << Type
        // If ?m is assigned to the identity function (fun x, x), then the constraint can be solved.
        if (a.kind() != b.kind() && !is_metavar(a) && !is_metavar(b) && !(is_app(a) && has_metavar(arg(a, 0))) && !(is_app(b) && has_metavar(arg(b, 0)))) {
            m_conflict = justification(new unification_failure_justification(c));
            return false;
        }

        if (m_quota < 0) {
            // process expensive cases
            if (process_meta_app(a, b, true, c) || process_meta_app(b, a, false, c))
                return true;
        }

        if (m_quota < - static_cast<int>(m_state.m_queue.size())) {
            // std::cout << "\n\nTRYING EXPENSIVE STEP...\n";
            // display(std::cout);
            // process very expensive cases
            if (process_lower(a, b, c) ||
                process_upper(a, b, c) ||
                process_metavar_inst(a, b, true, c) ||
                process_metavar_inst(b, a, false, c) ||
                process_metavar_lift_abstraction(a, b, c) ||
                process_metavar_lift_abstraction(b, a, c) ||
                process_meta_app(a, b, true, c, true))
                return true;
        }

        // std::cout << "Postponed: "; display(std::cout, c);
        push_back(c);

        return true;
    }


    bool process_max(unification_constraint const & c) {
        expr lhs1 = max_lhs1(c);
        expr lhs2 = max_lhs2(c);
        expr const & rhs  = max_rhs(c);
        buffer<justification> jsts;
        bool modified = false;
        expr new_lhs1 = lhs1;
        expr new_lhs2 = lhs2;
        expr new_rhs  = rhs;
        if (has_assigned_metavar(lhs1)) {
            new_lhs1 = instantiate_metavars(lhs1, jsts);
            modified = true;
        }
        if (has_assigned_metavar(lhs2)) {
            new_lhs2 = instantiate_metavars(lhs2, jsts);
            modified = true;
        }
        if (has_assigned_metavar(rhs)) {
            new_rhs = instantiate_metavars(rhs, jsts);
            modified = true;
        }
        if (modified) {
            justification new_jst = mk_subst_justification(c, jsts);
            push_front(mk_max_constraint(get_context(c), new_lhs1, new_lhs2, new_rhs, new_jst));
            return true;
        }
        if (!is_metavar(lhs1) && !is_type(lhs1)) {
            new_lhs1 = normalize(get_context(c), lhs1);
            modified = (lhs1 != new_lhs1);
        }
        if (!is_metavar(lhs2) && !is_type(lhs2)) {
            new_lhs2 = normalize(get_context(c), lhs2);
            modified = (lhs2 != new_lhs2);
        }
        if (!is_metavar(rhs) && !is_type(rhs)) {
            new_rhs = normalize(get_context(c), rhs);
            modified = (rhs != new_rhs);
        }
        if (modified) {
            justification new_jst(new normalize_justification(c));
            push_front(mk_max_constraint(get_context(c), new_lhs1, new_lhs2, new_rhs, new_jst));
            return true;
        }
        if (is_bool(lhs1))
            lhs1 = Type();
        if (is_bool(lhs2))
            lhs2 = Type();
        if (is_type(lhs1) && is_type(lhs2)) {
            justification new_jst(new normalize_justification(c));
            expr new_lhs = mk_type(max(ty_level(lhs1), ty_level(lhs2)));
            push_front(mk_eq_constraint(get_context(c), new_lhs, rhs, new_jst));
            return true;
        }
        if (lhs1 == rhs) {
            // ctx |- max(lhs1, lhs2) == rhs
            // ==>  IF lhs1 = rhs
            // ctx |- lhs2 << rhs
            justification new_jst(new normalize_justification(c));
            push_front(mk_convertible_constraint(get_context(c), lhs2, rhs, new_jst));
            return true;
        } else if (lhs2 == rhs) {
            // ctx |- max(lhs1, lhs2) == rhs
            // ==>  IF lhs1 = rhs
            // ctx |- lhs2 << rhs
            justification new_jst(new normalize_justification(c));
            push_front(mk_convertible_constraint(get_context(c), lhs1, rhs, new_jst));
            return true;
        }

        if ((!has_metavar(lhs1) && !is_type(lhs1)) ||
            (!has_metavar(lhs2) && !is_type(lhs2))) {
            m_conflict = justification(new unification_failure_justification(c));
            return false;
        }

        // std::cout << "Postponed: "; display(std::cout, c);
        push_back(c);
        return true;
    }

    bool process_choice(unification_constraint const & c) {
        std::unique_ptr<case_split> new_cs(new choice_case_split(c, m_state));
        bool r = new_cs->next(*this);
        lean_assert(r);
        m_case_splits.push_back(std::move(new_cs));
        return r;
    }

    void resolve_conflict() {
        lean_assert(m_conflict);

        // std::cout << "Resolve conflict, num case_splits: " << m_case_splits.size() << "\n";
        // formatter fmt = mk_simple_formatter();
        // std::cout << m_conflict.pp(fmt, options(), nullptr, true) << "\n";

        while (!m_case_splits.empty()) {
            std::unique_ptr<case_split> & d = m_case_splits.back();
            // std::cout << "Assumption " << d->m_curr_assumption.pp(fmt, options(), nullptr, true) << "\n";
            if (depends_on(m_conflict, d->m_curr_assumption)) {
                d->m_failed_justifications.push_back(m_conflict);
                if (d->next(*this)) {
                    m_conflict = justification();
                    reset_quota();
                    return;
                }
            }
            m_case_splits.pop_back();
        }
        throw elaborator_exception(m_conflict);
    }

    bool next_choice_case(choice_case_split & s) {
        unification_constraint & choice = s.m_choice;
        unsigned idx = s.m_idx;
        if (idx < choice_size(choice)) {
            s.m_idx++;
            s.m_curr_assumption = mk_assumption();
            m_state = s.m_prev_state;
            push_front(mk_eq_constraint(get_context(choice), choice_mvar(choice), choice_ith(choice, idx), s.m_curr_assumption));
            return true;
        } else {
            m_conflict = justification(new unification_failure_by_cases_justification(choice, s.m_failed_justifications.size(), s.m_failed_justifications.data()));
            return false;
        }
    }

    bool next_generic_case(generic_case_split & s) {
        unsigned idx = s.m_idx;
        unsigned sz  = s.m_states.size();
        if (idx < sz) {
            s.m_idx++;
            s.m_curr_assumption = s.m_assumptions[sz - idx - 1];
            m_state             = s.m_states[sz - idx - 1];
            return true;
        } else {
            m_conflict = justification(new unification_failure_by_cases_justification(s.m_constraint, s.m_failed_justifications.size(), s.m_failed_justifications.data()));
            return false;
        }
    }

    bool next_plugin_case(plugin_case_split & s) {
        try {
            s.m_curr_assumption = mk_assumption();
            std::pair<metavar_env, list<unification_constraint>> r = s.m_alternatives->next(s.m_curr_assumption);
            m_state.m_queue     = s.m_prev_state.m_queue;
            m_state.m_menv      = r.first;
            for (auto c : r.second) {
                push_front(c);
            }
            return true;
        } catch (exception & ex) {
            m_conflict = justification(new unification_failure_by_cases_justification(s.m_constraint, s.m_failed_justifications.size(), s.m_failed_justifications.data()));
            return false;
        }
    }

public:
    imp(environment const & env, metavar_env const & menv, unsigned num_cnstrs, unification_constraint const * cnstrs,
        options const & opts, std::shared_ptr<elaborator_plugin> const & p):
        m_env(env),
        m_type_inferer(env),
        m_normalizer(env),
        m_state(menv, num_cnstrs, cnstrs),
        m_plugin(p) {
        set_options(opts);
        m_next_id     = 0;
        m_quota       = 0;
        m_first       = true;
        // display(std::cout);
    }

    metavar_env next() {
        check_interrupted();
        if (m_conflict)
            throw elaborator_exception(m_conflict);
        if (!m_case_splits.empty()) {
            buffer<justification> assumptions;
            for (std::unique_ptr<case_split> const & cs : m_case_splits)
                assumptions.push_back(cs->m_curr_assumption);
            m_conflict = justification(new next_solution_justification(assumptions.size(), assumptions.data()));
            resolve_conflict();
        } else if (m_first) {
            m_first = false;
        } else {
            // this is not the first run, and there are no case-splits
            m_conflict = justification(new next_solution_justification(0, nullptr));
            throw elaborator_exception(m_conflict);
        }
        reset_quota();
        while (true) {
            check_interrupted();
            cnstr_queue & q = m_state.m_queue;
            if (q.empty() || m_quota < - static_cast<int>(q.size()) - 10) {
                // TODO(Leo): improve exit condition
                return m_state.m_menv;
            } else {
                unification_constraint c = q.front();
                // std::cout << "Processing, quota: " << m_quota << ", depth: " << m_case_splits.size() << " "; display(std::cout, c);
                q.pop_front();
                if (!process(c)) {
                    resolve_conflict();
                }
            }
        }
    }

    void display(std::ostream & out, unification_constraint const & c) const {
        formatter fmt = mk_simple_formatter();
        out << c.pp(fmt, options(), nullptr, false) << "\n";
    }

    void display(std::ostream & out) const {
        m_state.m_menv.for_each_subst([&](name const & m, expr const & e) {
                out << m << " <- " << e << "\n";
            });
        for (auto c : m_state.m_queue)
            display(out, c);
    }
};

elaborator::elaborator(environment const & env,
                       metavar_env const & menv,
                       unsigned num_cnstrs,
                       unification_constraint const * cnstrs,
                       options const & opts,
                       std::shared_ptr<elaborator_plugin> const & p):
    m_ptr(new imp(env, menv, num_cnstrs, cnstrs, opts, p)) {
}

elaborator::elaborator(environment const & env,
                       metavar_env const & menv,
                       context const & ctx, expr const & lhs, expr const & rhs):
    elaborator(env, menv, { mk_eq_constraint(ctx, lhs, rhs, justification()) }) {
}

elaborator::~elaborator() {
}

metavar_env elaborator::next() {
    return m_ptr->next();
}
}
