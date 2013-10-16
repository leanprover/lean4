/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <vector>
#include <utility>
#include "util/pdeque.h"
#include "kernel/formatter.h"
#include "kernel/free_vars.h"
#include "kernel/normalizer.h"
#include "kernel/instantiate.h"
#include "kernel/builtin.h"
#include "library/light_checker.h"
#include "library/update_expr.h"
#include "library/reduce.h"
#include "library/elaborator/elaborator.h"
#include "library/elaborator/elaborator_trace.h"

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
        trace              m_curr_assumption; // trace object used to justify current split
        state              m_prev_state;
        std::vector<trace> m_failed_traces;   // traces/justifications for failed branches

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
       \brief Case split object for higher-order matching
    */
    struct ho_match_case_split : public case_split {
        unification_constraint m_constraint;
        unsigned               m_idx;    // current alternative
        std::vector<state>     m_states; // set of alternatives

        ho_match_case_split(unification_constraint const & cnstr, unsigned num_states, state const * states, state const & prev_state):
            case_split(prev_state),
            m_constraint(cnstr),
            m_idx(0),
            m_states(states, states + num_states) {
        }

        virtual ~ho_match_case_split() {}

        virtual bool next(imp & owner) {
            return owner.next_ho_case(*this);
        }
    };

    struct synthesizer_case_split : public case_split {
        expr                                 m_metavar;
        std::unique_ptr<synthesizer::result> m_alternatives;

        synthesizer_case_split(expr const & m, std::unique_ptr<synthesizer::result> & r, state const & prev_state):
            case_split(prev_state),
            m_metavar(m),
            m_alternatives(std::move(r)) {
        }

        virtual ~synthesizer_case_split() {}
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
    light_checker                            m_type_infer;
    normalizer                               m_normalizer;
    state                                    m_state;
    std::vector<std::unique_ptr<case_split>> m_case_splits;
    std::shared_ptr<synthesizer>             m_synthesizer;
    std::shared_ptr<elaborator_plugin>       m_plugin;
    unsigned                                 m_next_id;
    int                                      m_quota;
    trace                                    m_conflict;
    bool                                     m_interrupted;


    // options
    bool                                     m_use_traces;
    bool                                     m_use_normalizer;

    void set_options(options const &) {
        m_use_traces     = true;
        m_use_normalizer = true;
    }

    void reset_quota() {
        m_quota = m_state.m_queue.size();
    }

    trace mk_assumption() {
        unsigned id = m_next_id;
        m_next_id++;
        return trace(new assumption_trace(id));
    }

    /** \brief Add given constraint to the front of the current constraint queue */
    void push_front(unification_constraint const & c) {
        reset_quota();
        m_state.m_queue.push_front(c);
    }

    /** \brief Return true iff \c m is an assigned metavariable in the current state */
    bool is_assigned(expr const & m) const {
        lean_assert(is_metavar(m));
        return m_state.m_menv.is_assigned(m);
    }

    /** \brief Return the substitution for an assigned metavariable */
    expr get_mvar_subst(expr const & m) const {
        lean_assert(is_metavar(m));
        lean_assert(is_assigned(m));
        return m_state.m_menv.get_subst(m);
    }

    /** \brief Return the trace/justification for an assigned metavariable */
    trace get_mvar_trace(expr const & m) const {
        lean_assert(is_metavar(m));
        lean_assert(is_assigned(m));
        return m_state.m_menv.get_trace(m);
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
        return ::lean::has_metavar(e, m, m_state.m_menv.get_substitutions());
    }

    /**
        \brief Return a unassigned metavariable in the current state.
        Return the anonymous name if the state does not contain unassigned metavariables.
    */
    name find_unassigned_metavar() const {
        return m_state.m_menv.find_unassigned_metavar();
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
            r = mk_lambda(name(g_x_name, i), types[i], r);
        }
        return r;
    }

    /**
       \brief Auxiliary method for pushing a new constraint to the constraint queue.
       The new constraint is based on the constraint \c c. The constraint \c c may be a equality or convertability constraint.
       The update is justified by \c new_tr.
    */
    void push_updated_constraint(unification_constraint const & c, expr const & new_a, expr const & new_b, trace const & new_tr) {
        lean_assert(is_eq(c) || is_convertible(c));
        context const & ctx = get_context(c);
        if (is_eq(c))
            push_front(mk_eq_constraint(ctx, new_a, new_b, new_tr));
        else
            push_front(mk_convertible_constraint(ctx, new_a, new_b, new_tr));
    }

    /**
       \brief Auxiliary method for pushing a new constraint to the constraint queue.
       The new constraint is based on the constraint \c c. The constraint \c c may be a equality or convertability constraint.
       The flag \c is_lhs says if the left-hand-side or right-hand-side are being updated with \c new_a.
       The update is justified by \c new_tr.
    */
    void push_updated_constraint(unification_constraint const & c, bool is_lhs, expr const & new_a, trace const & new_tr) {
        lean_assert(is_eq(c) || is_convertible(c));
        context const & ctx = get_context(c);
        if (is_eq(c)) {
            if (is_lhs)
                push_front(mk_eq_constraint(ctx, new_a, eq_rhs(c), new_tr));
            else
                push_front(mk_eq_constraint(ctx, eq_lhs(c), new_a, new_tr));
        } else {
            if (is_lhs)
                push_front(mk_convertible_constraint(ctx, new_a, convertible_to(c), new_tr));
            else
                push_front(mk_convertible_constraint(ctx, convertible_from(c), new_a, new_tr));
        }
    }

    /**
       \brief Auxiliary method for pushing a new constraint to the constraint queue.
       The new constraint is obtained from \c c by one or more normalization steps that produce \c new_a and \c new_b
    */
    void push_normalized_constraint(unification_constraint const & c, expr const & new_a, expr const & new_b) {
        push_updated_constraint(c, new_a, new_b, trace(new normalize_trace(c)));
    }

    /**
       \brief Assign \c v to \c m with justification \c tr in the current state.
    */
    void assign(expr const & m, expr const & v, trace const & tr) {
        lean_assert(is_metavar(m));
        metavar_env & menv = m_state.m_menv;
        m_state.m_menv.assign(m, v, tr);
        if (menv.has_type(m)) {

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
        lean_unreachable();
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
    status process_metavar(unification_constraint const & c, expr const & a, expr const & b, bool is_lhs, bool allow_assignment) {
        if (is_metavar(a)) {
            if (is_assigned(a)) {
                // Case 1
                trace new_tr(new substitution_trace(c, get_mvar_trace(a)));
                push_updated_constraint(c, is_lhs, get_mvar_subst(a), new_tr);
                return Processed;
            } else if (!has_local_context(a)) {
                // Case 2
                if (has_metavar(b, a)) {
                    m_conflict = trace(new unification_failure_trace(c));
                    return Failed;
                } else if (allow_assignment) {
                    assign(a, b, trace(new assignment_trace(c)));
                    reset_quota();
                    return Processed;
                }
            } else {
                local_entry const & me = head(metavar_lctx(a));
                if (me.is_lift() && !has_free_var(b, me.s(), me.s() + me.n())) {
                    // Case 3
                    trace new_tr(new substitution_trace(c, get_mvar_trace(a)));
                    expr new_a = pop_meta_context(a);
                    expr new_b = lower_free_vars(b, me.s() + me.n(), me.n());
                    if (!is_lhs)
                        swap(new_a, new_b);
                    push_updated_constraint(c, new_a, new_b, new_tr);
                    return Processed;
                }
            }
        }

        if (is_app(a) && is_metavar(arg(a, 0)) && is_assigned(arg(a, 0))) {
            // Case 4
            trace new_tr(new substitution_trace(c, get_mvar_trace(arg(a, 0))));
            expr new_a = update_app(a, 0, get_mvar_subst(arg(a, 0)));
            push_updated_constraint(c, is_lhs, new_a, new_tr);
            return Processed;
        }
        return Continue;
    }


    /** \brief Unfold let-expression */
    void process_let(expr & a) {
        if (is_let(a))
            a = instantiate(let_body(a), let_value(a));
    }

    /** \brief Replace variables by their definition if the context contains it. */
    void process_var(context const & ctx, expr & a) {
        if (is_var(a)) {
            try {
                context_entry const & e = lookup(ctx, var_idx(a));
                if (e.get_body())
                    a = e.get_body();
            } catch (exception&) {
            }
        }
    }

    expr normalize(context const & ctx, expr const & a) {
        return m_normalizer(a, ctx, &(m_state.m_menv));
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
                        if (to_value(f).normalize(new_args.size(), new_args.data(), r)) {
                            a = r;
                            return;
                        }
                    }
                }
                if (modified) {
                    a = mk_app(new_args.size(), new_args.data());
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
        object const & obj = m_env.find_object(const_name(a));
        if (obj && obj.is_definition() && !obj.is_opaque())
            return obj.get_weight();
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
            return m_env.find_object(const_name(a)).get_value();
        } else {
            return update_app(a, 0, m_env.find_object(const_name(arg(a, 0))).get_value());
        }
    }

    bool normalize_head(expr a, expr b, unification_constraint const & c) {
        context const & ctx = get_context(c);
        bool modified = false;
        while (true) {
            check_interrupted(m_interrupted);
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

    bool process_eq_convertible(context const & ctx, expr const & a, expr const & b, unification_constraint const & c) {
        bool eq = is_eq(c);
        if (a == b) {
            return true;
        }

        status r;
        bool allow_assignment = eq; // at this point, we only assign metavariables if the constraint is an equational constraint.
        r = process_metavar(c, a, b, true, allow_assignment);
        if (r != Continue) { return r == Processed; }
        r = process_metavar(c, b, a, false, allow_assignment);
        if (r != Continue) { return r == Processed; }

        if (normalize_head(a, b, c)) { return true; }

        r = process_metavar(c, a, b, true, !is_type(b) && !is_meta(b));
        if (r != Continue) { return r == Processed; }
        r = process_metavar(c, b, a, false, !is_type(a) && !is_meta(a) && a != Bool);
        if (r != Continue) { return r == Processed; }

        if (a.kind() == b.kind()) {
            switch (a.kind()) {
            case expr_kind::Constant: case expr_kind::Var: case expr_kind::Value:
                return a == b;
            case expr_kind::Type:
                if ((!eq && m_env.is_ge(ty_level(b), ty_level(a))) || (eq && a == b)) {
                    return true;
                } else {
                    m_conflict = trace(new unification_failure_trace(c));
                    return false;
                }
            case expr_kind::Eq: {
                trace new_trace(new destruct_trace(c));
                push_front(mk_eq_constraint(ctx, eq_lhs(a), eq_lhs(b), new_trace));
                push_front(mk_eq_constraint(ctx, eq_rhs(a), eq_rhs(b), new_trace));
                return true;
            }
            case expr_kind::Pi: {
                trace new_trace(new destruct_trace(c));
                push_front(mk_eq_constraint(ctx, abst_domain(a), abst_domain(b), new_trace));
                context new_ctx = extend(ctx, abst_name(a), abst_domain(a));
                if (eq)
                    push_front(mk_eq_constraint(new_ctx, abst_body(a), abst_body(b), new_trace));
                else
                    push_front(mk_convertible_constraint(new_ctx, abst_body(a), abst_body(b), new_trace));
                return true;
            }
            case expr_kind::Lambda: {
                trace new_trace(new destruct_trace(c));
                push_front(mk_eq_constraint(ctx, abst_domain(a), abst_domain(b), new_trace));
                context new_ctx = extend(ctx, abst_name(a), abst_domain(a));
                push_front(mk_eq_constraint(new_ctx, abst_body(a), abst_body(b), new_trace));
                return true;
            }
            case expr_kind::App:
                if (!is_meta_app(a) && !is_meta_app(b)) {
                    if (num_args(a) == num_args(b)) {
                        trace new_trace(new destruct_trace(c));
                        for (unsigned i = 0; i < num_args(a); i++)
                            push_front(mk_eq_constraint(ctx, arg(a, i), arg(b, i), new_trace));
                        return true;
                    } else {
                        return false;
                    }
                }
                break;
            case expr_kind::Let:
                lean_unreachable();
                return true;
            default:
                break;
            }
        }

        if (!is_meta(a) && !is_meta(b) && a.kind() != b.kind())
            return false;

        std::cout << "Postponed: "; display(std::cout, c);

        return true;
    }


    bool process_max(unification_constraint const &) {
        // TODO(Leo)
        return true;
    }

    bool process_choice(unification_constraint const &) {
        // TODO(Leo)
        return true;
    }

    void resolve_conflict() {
        lean_assert(m_conflict);
        while (!m_case_splits.empty()) {
            std::unique_ptr<case_split> & d = m_case_splits.back();
            if (depends_on(m_conflict, d->m_curr_assumption)) {
                d->m_failed_traces.push_back(m_conflict);
                if (d->next(*this)) {
                    m_conflict = trace();
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
            s.m_idx++;
            return true;
        } else {
            m_conflict = trace(new unification_failure_by_cases_trace(choice, s.m_failed_traces.size(), s.m_failed_traces.data()));
            return false;
        }
    }

    bool next_ho_case(ho_match_case_split &) {
#if 0
        unification_constraint & cnstr = s.m_constraint;
        context const & ctx = get_context(cnstr);
        expr const & a      = eq_lhs(cnstr);
        expr const & b      = eq_rhs(cnstr);
        lean_assert(is_meta_app(a));
        lean_assert(!has_local_context(arg(a, 0)));
        lean_assert(!is_meta_app(b));
        expr f_a       = arg(a, 0);
        lean_assert(is_metavar(f_a));
        unsigned num_a = num_args(a);



        // unification_constraints_wrapper ucw;
        buffer<expr> arg_types;
        for (unsigned i = 1; i < num_a; i++) {
            arg_types.push_back(m_type_infer(arg(a, i), ctx, &s, &ucw));
        }
#endif
        return true;
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
            m_conflict = trace(new unification_failure_by_cases_trace(s.m_constraint, s.m_failed_traces.size(), s.m_failed_traces.data()));
            return false;
        }
    }

public:
    imp(environment const & env, metavar_env const & menv, unsigned num_cnstrs, unification_constraint const * cnstrs,
        options const & opts, std::shared_ptr<synthesizer> const & s, std::shared_ptr<elaborator_plugin> const & p):
        m_env(env),
        m_type_infer(env),
        m_normalizer(env),
        m_state(menv, num_cnstrs, cnstrs),
        m_synthesizer(s),
        m_plugin(p) {
        set_options(opts);
        m_next_id     = 0;
        m_quota       = 0;
        m_interrupted = false;

        display(std::cout);
    }

    substitution next() {
        check_interrupted(m_interrupted);
        if (m_conflict)
            throw elaborator_exception(m_conflict);
        if (!m_case_splits.empty()) {
            buffer<trace> assumptions;
            for (std::unique_ptr<case_split> const & cs : m_case_splits)
                assumptions.push_back(cs->m_curr_assumption);
            m_conflict = trace(new next_solution_trace(assumptions.size(), assumptions.data()));
            resolve_conflict();
        }
        reset_quota();
        while (true) {
            check_interrupted(m_interrupted);
            cnstr_queue & q = m_state.m_queue;
            if (q.empty()) {
                name m = find_unassigned_metavar();
                std::cout << "Queue is empty\n"; display(std::cout);
                if (m) {
                    // TODO(Leo)
                    // erase the following line, and implement interface with synthesizer
                    return m_state.m_menv.get_substitutions();
                } else {
                    return m_state.m_menv.get_substitutions();
                }
            } else {
                unification_constraint c = q.front();
                std::cout << "Processing "; display(std::cout, c);
                q.pop_front();
                if (!process(c)) {
                    resolve_conflict();
                }
            }
        }
    }

    void interrupt() {
        m_interrupted = true;
        m_type_infer.set_interrupt(true);
        m_normalizer.set_interrupt(true);
    }

    void display(std::ostream & out, unification_constraint const & c) const {
        formatter fmt = mk_simple_formatter();
        out << c.pp(fmt, options(), nullptr, false) << "\n";
    }

    void display(std::ostream & out) const {
        m_state.m_menv.get_substitutions().for_each([&](name const & m, expr const & e) {
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
                       std::shared_ptr<synthesizer> const & s,
                       std::shared_ptr<elaborator_plugin> const & p):
    m_ptr(new imp(env, menv, num_cnstrs, cnstrs, opts, s, p)) {
}

elaborator::elaborator(environment const & env,
                       metavar_env const & menv,
                       context const & ctx, expr const & lhs, expr const & rhs):
    elaborator(env, menv, { mk_eq_constraint(ctx, lhs, rhs, trace()) }) {
}

elaborator::~elaborator() {
}

substitution elaborator::next() {
    return m_ptr->next();
}

void elaborator::interrupt() {
    m_ptr->interrupt();
}
}
