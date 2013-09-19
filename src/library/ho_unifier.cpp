/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/pvector.h"
#include "util/pdeque.h"
#include "util/exception.h"
#include "kernel/environment.h"
#include "kernel/free_vars.h"
#include "kernel/instantiate.h"
#include "kernel/normalizer.h"
#include "library/light_checker.h"
#include "library/reduce.h"
#include "library/update_expr.h"
#include "library/ho_unifier.h"
#include "library/printer.h"

namespace lean {
static name g_x_name("x");
class ho_unifier::imp {
    typedef std::tuple<context, expr, expr> constraint;
    typedef pdeque<constraint>              cqueue; // constraint queue
    struct state {
        unsigned    m_id;
        metavar_env m_subst;
        cqueue      m_queue;
        state(unsigned id, metavar_env const & menv, cqueue const & q):
            m_id(id), m_subst(menv), m_queue(q) {}
    };
    typedef std::vector<state>              state_stack;

    environment    m_env;
    normalizer     m_normalizer;
    light_checker  m_type_infer;
    state_stack    m_state_stack;
    unsigned       m_delayed;
    unsigned       m_next_state_id;
    bool           m_ho; // true if used higher-order
    volatile bool  m_interrupted;

    static metavar_env & subst_of(state & s) { return s.m_subst; }
    static cqueue & queue_of(state & s) { return s.m_queue; }

    state mk_state(metavar_env const & s, cqueue const & q) {
        unsigned id = m_next_state_id;
        m_next_state_id++;
        return state(id, s, q);
    }

    void reset_delayed() {
        m_delayed = 0;
    }

    /**
       \brief Add a constraint to the state in the top of the state_stack
    */
    void add_constraint(context const & ctx, expr const & l, expr const & r) {
        lean_assert(!m_state_stack.empty());
        state & s = m_state_stack.back();
        queue_of(s).push_front(constraint(ctx, l, r));
        reset_delayed();
    }

    /**
       \brief Add a constraint to the state in the top of the state_stack,
       but put the constraint in the end of the queue, and increase the m_delayed counter.
    */
    void postpone_constraint(context const & ctx, expr const & l, expr const & r) {
        lean_assert(!m_state_stack.empty());
        state & s = m_state_stack.back();
        queue_of(s).push_back(constraint(ctx, l, r));
        m_delayed++;
    }

    void init(context const & ctx, expr const & l, expr const & r, metavar_env const & menv) {
        m_next_state_id = 0;
        m_ho = false;
        m_state_stack.clear();
        m_state_stack.push_back(mk_state(menv, cqueue()));
        add_constraint(ctx, l, r);
    }

    metavar_env cleanup_subst(metavar_env const & s, unsigned num_input_metavars) {
        // eliminate auxiliary metavariables
        if (!m_ho) {
            return s;
        } else {
            metavar_env new_s;
            for (unsigned i = 0; i < num_input_metavars; i++) {
                new_s.mk_metavar(s.get_type(i), s.get_context(i));
                expr subst = s.get_subst(i);
                if (subst)
                    new_s.assign(i, subst);
            }
            return new_s;
        }
    }

    list<result> save_result(list<result> const & r, metavar_env const & s, residue const & rs, unsigned num_input_metavars) {
        return cons(result(cleanup_subst(s, num_input_metavars), rs), r);
    }

    /**
       Process <tt>a == b</tt> when:
       1- \c a is an assigned metavariable
       2- \c a is a unassigned metavariable without a metavariable context.
       3- \c a is a unassigned metavariable of the form <tt>?m[lift:s:n, ...]</tt>, and \c b does not have
          a free variable in the range <tt>[s, s+n)</tt>.
       4- \c a is an application of the form <tt>(?m ...)</tt> where ?m is an assigned metavariable.
    */
    enum status { Solved, Failed, Continue };
    status process_metavar(expr & a, expr & b, metavar_env & s) {
        if (is_metavar(a)) {
            if (s.is_assigned(a)) {
                // Case 1
                a = s.get_subst(a);
            } else if (!has_meta_context(a)) {
                // Case 2
                if (has_metavar(b, a, s)) {
                    return Failed;
                } else {
                    s.assign(a, b);
                    reset_delayed();
                    return Solved;
                }
            } else {
                meta_entry const & me = head(metavar_ctx(a));
                if (me.is_lift() && !has_free_var(b, me.s(), me.s() + me.n())) {
                    // Case 3
                    b = lower_free_vars(b, me.s() + me.n(), me.n());
                    a = pop_meta_context(a);
                }
            }
        }

        if (is_app(a) && is_metavar(arg(a, 0)) && s.is_assigned(arg(a, 0))) {
            // Case 4
            a = update_app(a, 0, s.get_subst(arg(a, 0)));
        }
        return Continue;
    }

    /** \brief Unfold let-expression */
    void process_let(expr & a) {
        if (is_let(a))
            a = instantiate(let_body(a), let_value(a));
    }

    /** \brief Unfold constants */
    void process_constant(expr & a) {
        if (is_constant(a)) {
            object const & obj = m_env.find_object(const_name(a));
            if (obj && obj.is_definition() && !obj.is_opaque())
                a = obj.get_value();
        }
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

    /** \brief Applies simple unfolding steps */
    void process_simple(context const & ctx, expr & a) {
        process_let(a);
        process_constant(a);
        process_var(ctx, a);
    }

    /** \brief Process the application's function using \c process_simple */
    void process_app_function(context const & ctx, expr & a) {
        if (is_app(a)) {
            expr f = arg(a, 0);
            process_simple(ctx, f);
            a = update_app(a, 0, f);
        }
    }

    /** \brief Creates a subproblem based on the application arguments */
    bool process_app_args(context const & ctx, expr const & a, expr const & b, unsigned start) {
        lean_assert(is_app(a) && is_app(b));
        if (num_args(a) != num_args(b)) {
            return false;
        } else {
            for (unsigned i = 1; i < num_args(a); i++) {
                add_constraint(ctx, arg(a, i), arg(b, i));
            }
            return true;
        }
    }

    /**
       Process a constraint <tt>ctx |- a = b</tt>, where \c a and \c b
       are applications and the function is the same.
       That is, <tt>arg(a, 0) == arg(b, 0)</tt>

       \pre is_app(a) && is_app(b) && arg(a, 0) == arg(b, 0)
    */
    bool process_easy_app(context const & ctx, expr const & a, expr const & b) {
        lean_assert(is_app(a) && is_app(b) && arg(a, 0) == arg(b, 0));
        return process_app_args(ctx, a, b, 1);
    }

    /** \brief Return true if \c a is of the form <tt>(?m ...)</tt> */
    bool is_meta_app(expr const & a) {
        return is_app(a) && is_metavar(arg(a, 0));
    }

    /**
       Auxiliary class for invoking m_type_infer.
       If it creates a new unfication problem we mark m_failed to true.
       add_eq can be easily supported, but we need to extend ho_unifier API to be able
       to support add_type_of_eq and add_is_convertible.
       The m_type_infer only invokes add_type_of_eq when it needs to ask for the type
       of a metavariable that does not have a type yet.
       One possible workaround it o make sure that every metavariable has an associated type
       before invoking ho_unifier.
    */
    class unification_problems_wrapper : public unification_problems {
        bool m_failed;
    public:
        unification_problems_wrapper():m_failed(false) {}
        virtual void add_eq(context const & ctx, expr const & lhs, expr const & rhs) { m_failed = true; }
        virtual void add_type_of_eq(context const & ctx, expr const & n, expr const & t) { m_failed = true; }
        virtual void add_is_convertible(context const & ctx, expr const & t1, expr const & t2) { m_failed = true; }
        bool failed() const { return m_failed; }
    };

    /**
       \brief Process a constraint <tt>ctx |- a = b</tt> where \c a is of the form <tt>(?m ...)</tt>.
       We perform a "case split" using "projection" or "imitation". See Huet&Lang's paper on higher order matching
       for further details.
    */
    bool process_meta_app(context const & ctx, expr const & a, expr const & b) {
        lean_assert(is_meta_app(a));
        lean_assert(!is_meta_app(b));
        m_ho = true; // using higher-order matching
        expr f_a          = arg(a, 0);
        lean_assert(is_metavar(f_a));
        state top_state   = m_state_stack.back();
        cqueue q          = queue_of(top_state);
        metavar_env s     = subst_of(top_state);
        unsigned midx     = metavar_idx(f_a);
        unsigned num_a    = num_args(a);
        unification_problems_wrapper upw;
        buffer<expr> arg_types;
        for (unsigned i = 1; i < num_a; i++) {
            arg_types.push_back(m_type_infer(arg(a, i), ctx, &s, &upw));
        }
        // clear the cache since we don't want a reference to s inside of m_type_infer
        m_type_infer.clear();
        if (upw.failed())
            return false;
        m_state_stack.pop_back();
        // add projections
        for (unsigned i = 1; i < num_a; i++) {
            expr proj = mk_var(i - 1);
            for (unsigned j = 1; j < num_a; j++)
                proj = mk_lambda(name(g_x_name, j), arg_types[j - 1], proj);
            cqueue new_q = q;
            new_q.push_front(constraint(ctx, arg(a, i), b));
            metavar_env new_s = s;
            new_s.assign(midx, proj);
            m_state_stack.push_back(mk_state(new_s, new_q));
        }
        // add imitation
        metavar_env new_s = s;
        cqueue  new_q     = q;
        if (is_app(b)) {
            expr f_b          = arg(b, 0);
            unsigned num_b    = num_args(b);
            buffer<expr> imitation_args; // arguments for the imitation
            imitation_args.push_back(f_b);
            for (unsigned i = 1; i < num_b; i++) {
                expr h_i = new_s.mk_metavar(ctx);
                buffer<expr> h_app_var_args;
                buffer<expr> h_app_subst_args;
                h_app_var_args.push_back(h_i);
                h_app_subst_args.push_back(h_i);
                for (unsigned j = 1; j < num_a; j++) {
                    h_app_var_args.push_back(mk_var(num_a - j - 1));
                    h_app_subst_args.push_back(arg(a, j));
                }
                imitation_args.push_back(mk_app(h_app_var_args.size(), h_app_var_args.data()));
                new_q.push_front(constraint(ctx, mk_app(h_app_subst_args.size(), h_app_subst_args.data()), arg(b, i)));
            }
            expr imitation = mk_app(imitation_args.size(), imitation_args.data());
            for (unsigned j = 1; j < num_a; j++)
                imitation = mk_lambda(name(g_x_name, j), arg_types[j - 1], imitation);
            new_s.assign(midx, imitation);
            m_state_stack.push_back(mk_state(new_s, new_q));
        } else {
            // TODO(Leo) handle eq like we handle applications
            // make f_a the constant function
            expr imitation = lift_free_vars(b, 0, num_a - 1);
            for (unsigned j = 1; j < num_a; j++)
                imitation = mk_lambda(name(g_x_name, j), arg_types[j - 1], imitation);
            new_s.assign(midx, imitation);
            m_state_stack.push_back(mk_state(new_s, new_q));
        }
        reset_delayed();
        return true;
    }

    /**
       \brief Process the constraint \c c. Return true if the constraint was processed or postponed, and false
       if it failed to solve the constraint.
    */
    bool process(constraint const & c, metavar_env & s) {
        context ctx = std::get<0>(c);
        expr const & old_a = std::get<1>(c);
        expr const & old_b = std::get<2>(c);
        expr a = old_a;
        expr b = old_b;
        if (a == b) {
            reset_delayed();
            return true;
        }
        if (is_app(a) && is_app(b) && arg(a, 0) == arg(b, 0))
            return process_easy_app(ctx, a, b);
        status r;
        r = process_metavar(a, b, s);
        if (r != Continue) { return r == Solved; }
        r = process_metavar(b, a, s);
        if (r != Continue) { return r == Solved; }
        process_simple(ctx, a);
        process_simple(ctx, b);
        process_app_function(ctx, a);
        process_app_function(ctx, b);
        if ((is_app(a) && !is_eqp(a, old_a)) || (is_app(b) && !is_eqp(b, old_b))) {
            // some progress was made
            add_constraint(ctx, a, b);
            return true;
        }
        a = head_beta_reduce(a);
        b = head_beta_reduce(b);
        if ((is_metavar(a) && has_meta_context(a)) ||
            (is_metavar(b) && has_meta_context(b))) {
            // a or b is a metavariable that has a metavariable context associated with it.
            // postpone
            postpone_constraint(ctx, a, b);
            return true;
        }
        if (!is_app(a) && !is_app(b)) {
            if (a.kind() != b.kind())
                return false;
            switch (a.kind()) {
            case expr_kind::Constant: case expr_kind::Var: case expr_kind::Value: case expr_kind::Type:
                return false;
            case expr_kind::Eq:
                add_constraint(ctx, eq_lhs(a), eq_lhs(b));
                add_constraint(ctx, eq_rhs(a), eq_rhs(b));
                return true;
            case expr_kind::Lambda: case expr_kind::Pi:
                add_constraint(ctx, abst_domain(a), abst_domain(b));
                add_constraint(extend(ctx, abst_name(a), abst_domain(a)), abst_body(a), abst_body(b));
                return true;
            case expr_kind::Let: case expr_kind::MetaVar: case expr_kind::App:
                lean_unreachable();
                return false;
            }
        }

        if (is_meta_app(a)) {
            if (is_meta_app(b)) {
                postpone_constraint(ctx, a, b);
                return true;
            } else {
                return process_meta_app(ctx, a, b);
                return true;
            }
        } else if (is_meta_app(b)) {
            lean_assert(!is_meta_app(b));
            return process_meta_app(ctx, b, a);
        }

        if (!is_eqp(a, old_a) || !is_eqp(b, old_b)) {
            // some progress was made
            add_constraint(ctx, a, b);
            return true;
        }

        expr norm_a = m_normalizer(a, ctx, &s);
        expr norm_b = m_normalizer(b, ctx, &s);
        if (norm_a.kind() != norm_b.kind())
            return false;
        if (is_app(norm_a)) {
            return process_app_args(ctx, norm_a, norm_b, 0);
        } else if (a == norm_a && b == norm_b) {
            return false;
        } else {
            // some progress was made
            add_constraint(ctx, norm_a, norm_b);
            return true;
        }
    }

public:
    imp(environment const & env):m_env(env), m_normalizer(env), m_type_infer(env) {
        m_interrupted = false;
        m_delayed     = 0;
    }

    list<result> unify(context const & ctx, expr const & a, expr const & b, metavar_env const & menv) {
        unsigned num_metavars = menv.size();
        init(ctx, a, b, menv);
        list<result> r;
        while (!m_state_stack.empty()) {
            check_interrupted(m_interrupted);
            state & top_state = m_state_stack.back();
            cqueue & cq       = queue_of(top_state);
            unsigned cq_size  = cq.size();
            if (cq.empty()) {
                // no constraints left to be solved
                r = save_result(r, subst_of(top_state), residue(), num_metavars);
                m_state_stack.pop_back();
            } else {
                // try cq_sz times to find a constraint that can be processed
                constraint c = cq.front();
                // std::cout << "solving (" << top_state.m_id << ") " << std::get<1>(c) << " === " << std::get<2>(c) << "\n";
                cq.pop_front();
                if (!process(c, subst_of(top_state))) {
                    // state can't be solved
                    reset_delayed();
                    m_state_stack.pop_back();
                }
                if (m_delayed > cq_size) {
                    // None of the constraints could be processed.
                    // So, we save the remaining constraints as a residue
                    residue rs;
                    for (auto c : cq)
                        rs = cons(c, rs);
                    r = save_result(r, subst_of(top_state), rs, num_metavars);
                    reset_delayed();
                    m_state_stack.pop_back();
                }
            }
        }
        return r;
    }

    void set_interrupt(bool flag) {
        m_interrupted = flag;
        m_normalizer.set_interrupt(flag);
        m_type_infer.set_interrupt(flag);
    }
};

ho_unifier::ho_unifier(environment const & env):m_ptr(new imp(env)) {}
ho_unifier::~ho_unifier() {}
void ho_unifier::set_interrupt(bool flag) { m_ptr->set_interrupt(flag); }
list<ho_unifier::result> ho_unifier::operator()(context const & ctx, expr const & l, expr const & r, metavar_env const & menv) {
    return m_ptr->unify(ctx, l, r, menv);
}
}
