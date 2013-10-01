/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/pvector.h"
#include "util/pdeque.h"
#include "util/exception.h"
#include "util/sexpr/options.h"
#include "kernel/environment.h"
#include "kernel/free_vars.h"
#include "kernel/instantiate.h"
#include "kernel/normalizer.h"
#include "kernel/printer.h"
#include "library/light_checker.h"
#include "library/reduce.h"
#include "library/update_expr.h"
#include "library/ho_unifier.h"

#ifndef LEAN_LIBRARY_HO_UNIFIER_MAX_SOLUTIONS
#define LEAN_LIBRARY_HO_UNIFIER_MAX_SOLUTIONS std::numeric_limits<unsigned>::max()
#endif

#ifndef LEAN_LIBRARY_HO_UNIFIER_REMOVE_DUPLICATES
#define LEAN_LIBRARY_HO_UNIFIER_REMOVE_DUPLICATES true
#endif

#ifndef LEAN_LIBRARY_HO_UNIFIER_USE_NORMALIZER
#define LEAN_LIBRARY_HO_UNIFIER_USE_NORMALIZER true
#endif

#ifndef LEAN_LIBRARY_HO_UNIFIER_USE_BETA
#define LEAN_LIBRARY_HO_UNIFIER_USE_BETA true
#endif

namespace lean {
static name g_library_ho_unifier_max_solutions     {"library", "ho_unifier", "max_solutions"};
static name g_library_ho_unifier_remove_duplicates {"library", "ho_unifier", "remove_duplicates"};
static name g_library_ho_unifier_use_normalizer    {"library", "ho_unifier", "use_normalizer"};
static name g_library_ho_unifier_use_beta          {"library", "ho_unifier", "use_beta"};

RegisterUnsignedOption(g_library_ho_unifier_max_solutions, LEAN_LIBRARY_HO_UNIFIER_MAX_SOLUTIONS,
                       "maximum number of solutions for each invocation of the higher-order unifier");
RegisterBoolOption(g_library_ho_unifier_remove_duplicates, LEAN_LIBRARY_HO_UNIFIER_REMOVE_DUPLICATES,
                   "remove duplicate solutions in the higher-order unification module");
RegisterBoolOption(g_library_ho_unifier_use_normalizer, LEAN_LIBRARY_HO_UNIFIER_USE_NORMALIZER,
                   "use normalizer in the higher-order unification module");
RegisterBoolOption(g_library_ho_unifier_use_beta, LEAN_LIBRARY_HO_UNIFIER_USE_BETA,
                   "use beta-reduction in the higher-order unification module");

unsigned get_ho_unifier_max_solutions(options const & opts) {
    return opts.get_unsigned(g_library_ho_unifier_max_solutions, LEAN_LIBRARY_HO_UNIFIER_MAX_SOLUTIONS);
}

bool get_ho_unifier_remove_duplicates(options const & opts) {
    return opts.get_bool(g_library_ho_unifier_remove_duplicates, LEAN_LIBRARY_HO_UNIFIER_REMOVE_DUPLICATES);
}

bool get_ho_unifier_use_normalizer(options const & opts) {
    return opts.get_bool(g_library_ho_unifier_use_normalizer, LEAN_LIBRARY_HO_UNIFIER_USE_NORMALIZER);
}

bool get_ho_unifier_use_beta(options const & opts) {
    return opts.get_bool(g_library_ho_unifier_use_beta, LEAN_LIBRARY_HO_UNIFIER_USE_BETA);
}

static name g_x_name("x");
class ho_unifier::imp {
    typedef std::tuple<context, expr, expr> constraint;
    typedef pdeque<constraint>              cqueue; // constraint queue
    struct state {
        unsigned      m_id;
        substitution  m_subst;
        cqueue        m_queue;
        state(unsigned id, substitution const & subst, cqueue const & q):
            m_id(id), m_subst(subst), m_queue(q) {}
    };
    typedef std::vector<state>              state_stack;

    environment    m_env;
    normalizer     m_normalizer;
    light_checker  m_type_infer;
    state_stack    m_state_stack;
    unsigned       m_delayed;
    unsigned       m_next_state_id;
    bool           m_used_aux_vars;
    volatile bool  m_interrupted;
    // options
    unsigned       m_max_solutions;
    bool           m_remove_duplicates;
    bool           m_use_normalizer;
    bool           m_use_beta;

    static substitution & subst_of(state & s) { return s.m_subst; }
    static cqueue & queue_of(state & s) { return s.m_queue; }

    state mk_state(substitution const & s, cqueue const & q) {
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

    void init(context const & ctx, expr const & l, expr const & r, substitution const & subst) {
        m_next_state_id = 0;
        m_used_aux_vars = false;
        m_state_stack.clear();
        m_state_stack.push_back(mk_state(subst, cqueue()));
        add_constraint(ctx, l, r);
    }

    /**
       \brief Return true iff \c r already contains the solution (s, rs).

       \remark We only check if \c rs is empty.

       \remark \c ini_s is the initial substitution set. \c s is an extension of \c ini_s
    */
    bool contains_solution(list<result> const & r, substitution const & /* s */, residue const & rs, substitution const & /* ini_s */ ) {
        return
            empty(rs) &&
            std::any_of(r.begin(), r.end(), [&](result const & prev) {
                    if (!empty(prev.second))
                        return false;
                    // TODO(Leo) metavar
                    // substitution const & prev_s = prev.first;
                    // if (s != prev_s)
                    //    return false;
                    // return true;
                    return false;
                });
    }

    /**
       \brief Cleanup the result (remove auxiliary metavariables created by higher-order matching)

       \remark \c ini_s is the initial substitution set. \c s is an extension of \c ini_s
    */
    substitution cleanup_subst(substitution const & s, substitution const & /* ini_s */) {
#if 0  // TODO(Leo) metavar
        metavar_env new_s;
        for (unsigned i = 0; i < ini_s.size(); i++) {
            new_s.mk_metavar(s.get_type(i), s.get_context(i));
            expr subst = s.get_subst(i);
            if (subst) {
                if (m_use_beta && !ini_s.is_assigned(i)) {
                    // beta-reduce the substitution in order to simplify expressions built using
                    // higher-order matching
                    subst = beta_reduce(subst);
                }
                new_s.assign(i, subst);
            }
        }
        return new_s;
#else
        return s;
#endif
    }

    /**
       \brief Store a result (s, rs) into r.
       If m_remove_duplicates is true, then we check if r does not already contains the solution (s, rs).
       In the current implementation, we only perform the check when rs is empty.

       \remark \c ini_s is the initial substitution set. \c s is an extension of \c ini_s
    */
    list<result> save_result(list<result> const & r, substitution s, residue const & rs, substitution const & ini_s) {
        if (empty(rs) && m_used_aux_vars) {
            // We only do the cleanup when we don't have a residue.
            // If we have a residue, we can only remove auxiliary metavariables that do not occur in rs
            s = cleanup_subst(s, ini_s);
        }

        if (m_remove_duplicates && contains_solution(r, s, rs, ini_s)) {
            return r;
        } else {
            return cons(result(s, rs), r);
        }
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
    status process_metavar(expr & a, expr & b, substitution & s) {
        if (is_metavar(a)) {
            if (s.is_assigned(a)) {
                // Case 1
                a = s.get_subst(a);
            } else if (!has_local_context(a)) {
                // Case 2
                if (has_metavar(b, a, s)) {
                    return Failed;
                } else {
                    s.assign(a, b);
                    reset_delayed();
                    return Solved;
                }
            } else {
                local_entry const & me = head(metavar_lctx(a));
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
            for (unsigned i = start; i < num_args(a); i++) {
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

    /** \brief Return true iff \c a is a metavariable and has a meta context. */
    bool is_metavar_with_context(expr const & a) {
        return is_metavar(a) && has_local_context(a);
    }

    /** \brief Return true if \c a is of the form <tt>(?m[...] ...)</tt> */
    bool is_meta_app_with_context(expr const & a) {
        return is_meta_app(a) && has_local_context(arg(a, 0));
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
    class unification_constraints_wrapper : public unification_constraints {
        bool m_failed;
    public:
        unification_constraints_wrapper():m_failed(false) {}
        virtual void add(context const &, expr const &, expr const &) { m_failed = true; }
        virtual void add_type_of(context const &, expr const &, expr const &) { m_failed = true; }
        bool failed() const { return m_failed; }
    };

    expr mk_lambda(name const & n, expr const & d, expr const & b) {
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
        return mk_app(args.size(), args.data());
    }

    /**
       \brief Process a constraint <tt>ctx |- a = b</tt> where \c a is of the form <tt>(?m ...)</tt>.
       We perform a "case split" using "projection" or "imitation". See Huet&Lang's paper on higher order matching
       for further details.
    */
    bool process_meta_app(context const & ctx, expr const & a, expr const & b) {
        lean_assert(is_meta_app(a));
        lean_assert(!has_local_context(arg(a, 0)));
        lean_assert(!is_meta_app(b));
        m_used_aux_vars    = true;
        expr f_a           = arg(a, 0);
        lean_assert(is_metavar(f_a));
        state top_state    = m_state_stack.back();
        cqueue q           = queue_of(top_state);
        substitution s    = subst_of(top_state);
        name const & mname = metavar_name(f_a);
        unsigned num_a     = num_args(a);
        unification_constraints_wrapper ucw;
        buffer<expr> arg_types;
        for (unsigned i = 1; i < num_a; i++) {
            arg_types.push_back(m_type_infer(arg(a, i), ctx, &s, &ucw));
        }
        // Clear m_type_infer cache since we don't want a reference to s inside of m_type_infer
        m_type_infer.clear();
        if (ucw.failed())
            return false;
        m_state_stack.pop_back();
        // Add projections
        for (unsigned i = 1; i < num_a; i++) {
            // Assign f_a <- fun (x_1 : T_0) ... (x_{num_a-1} : T_{num_a-1}), x_i
            cqueue new_q = q;
            new_q.push_front(constraint(ctx, arg(a, i), b));
            substitution new_s = s;
            expr proj           = mk_lambda(arg_types, mk_var(num_a - i - 1));
            new_s.assign(mname, proj);
            m_state_stack.push_back(mk_state(new_s, new_q));
        }
        // Add imitation
        substitution new_s = s;
        cqueue        new_q = q;
        if (is_app(b)) {
            // Imitation for applications
            expr f_b          = arg(b, 0);
            unsigned num_b    = num_args(b);
            // Assign f_a <- fun (x_1 : T_0) ... (x_{num_a-1} : T_{num_a-1}), f_b (h_1 x_1 ... x_{num_a-1}) ... (h_{num_b-1} x_1 ... x_{num_a-1})
            // New constraints (h_i a_1 ... a_{num_a-1}) == arg(b, i)
            buffer<expr> imitation_args; // arguments for the imitation
            imitation_args.push_back(f_b);
            for (unsigned i = 1; i < num_b; i++) {
                expr h_i; // = new_s.mk_metavar(ctx);
                imitation_args.push_back(mk_app_vars(h_i, num_a - 1));
                new_q.push_front(constraint(ctx, update_app(a, 0, h_i), arg(b, i)));
            }
            expr imitation = mk_lambda(arg_types, mk_app(imitation_args.size(), imitation_args.data()));
            new_s.assign(mname, imitation);
        } else if (is_eq(b)) {
            // Imitation for equality
            // Assign f_a <- fun (x_1 : T_0) ... (x_{num_a-1} : T_{num_a-1}), (h_1 x_1 ... x_{num_a-1}) = (h_2 x_1 ... x_{num_a-1})
            // New constraints (h_1 a_1 ... a_{num_a-1}) == eq_lhs(b)
            //                 (h_2 a_1 ... a_{num_a-1}) == eq_rhs(b)
            expr h_1; // = new_s.mk_metavar(ctx);
            expr h_2; // = new_s.mk_metavar(ctx);
            expr imitation = mk_lambda(arg_types, mk_eq(mk_app_vars(h_1, num_a - 1), mk_app_vars(h_2, num_a - 1)));
            new_s.assign(mname, imitation);
            new_q.push_front(constraint(ctx, update_app(a, 0, h_1), eq_lhs(b)));
            new_q.push_front(constraint(ctx, update_app(a, 0, h_2), eq_rhs(b)));
        } else if (is_abstraction(b)) {
            // Imitation for lambdas and Pis
            // Assign f_a <- fun (x_1 : T_0) ... (x_{num_a-1} : T_{num_a-1}),
            //                        fun (x_b : (?h_1 x_1 ... x_{num_a-1})), (?h_2 x_1 ... x_{num_a-1} x_b)
            // New constraints (h_1 a_1 ... a_{num_a-1}) == abst_domain(b)
            //                 (h_2 a_1 ... a_{num_a-1} x_b) == abst_body(b)
            expr h_1; // = new_s.mk_metavar(ctx);
            expr h_2; // = new_s.mk_metavar(ctx);
            expr imitation = mk_lambda(arg_types, update_abstraction(b, mk_app_vars(h_1, num_a - 1), mk_app_vars(h_2, num_a)));
            new_s.assign(mname, imitation);
            new_q.push_front(constraint(ctx, update_app(a, 0, h_1), abst_domain(b)));
            new_q.push_front(constraint(extend(ctx, abst_name(b), abst_domain(b)), mk_app(update_app(a, 0, h_2), Var(0)), abst_body(b)));
        } else {
            // "Dumb imitation" aka the constant function
            // Assign f_a <- fun (x_1 : T_0) ... (x_{num_a-1} : T_{num_a-1}), b
            expr imitation = mk_lambda(arg_types, lift_free_vars(b, 0, num_a - 1));
            new_s.assign(mname, imitation);
        }
        m_state_stack.push_back(mk_state(new_s, new_q));
        reset_delayed();
        return true;
    }

    /** \brief Return true if \c a is of the form ?m[inst:i t, ...] */
    bool is_metavar_inst(expr const & a) const {
        return is_metavar(a) && has_local_context(a) && head(metavar_lctx(a)).is_inst();
    }

    /**
       \brief Process a constraint <tt>ctx |- a = b</tt> where \c a is of the form <tt>?m[(inst:i t), ...]</tt>.
       We perform a "case split",
       Case 1) ?m == #i and t == b
       Case 2) imitate b
    */
    void process_metavar_inst(context const & ctx, expr const & a, expr const & b) {
        lean_assert(is_metavar_inst(a));
        lean_assert(!is_metavar_inst(b));
        lean_assert(!is_meta_app(b));
        m_used_aux_vars     = true;
        local_context  lctx = metavar_lctx(a);
        name const & mname  = metavar_name(a);
        unsigned i          = head(lctx).s();
        expr t              = head(lctx).v();
        state top_state     = m_state_stack.back();
        cqueue q            = queue_of(top_state);
        substitution s     = subst_of(top_state);
        m_state_stack.pop_back();
        {
            // Case 1
            substitution new_s = s;
            new_s.assign(mname, mk_var(i));
            cqueue new_q = q;
            new_q.push_front(constraint(ctx, t, b));
            m_state_stack.push_back(mk_state(new_s, new_q));
        }
        {
            // Case 2
            substitution new_s = s;
            cqueue        new_q = q;
            if (is_app(b)) {
                // Imitation for applications b == f(s_1, ..., s_k)
                // mname <- f(?h_1, ..., ?h_k)
                expr f_b          = arg(b, 0);
                unsigned num_b    = num_args(b);
                buffer<expr> imitation;
                imitation.push_back(f_b);
                for (unsigned i = 1; i < num_b; i++)
                    imitation.push_back(expr()); // new_s.mk_metavar(ctx));
                new_s.assign(mname, mk_app(imitation.size(), imitation.data()));
            } else if (is_eq(b)) {
                // Imitation for equality b == Eq(s1, s2)
                // mname <- Eq(?h_1, ?h_2)
                expr h_1; // = new_s.mk_metavar(ctx);
                expr h_2; // = new_s.mk_metavar(ctx);
                new_s.assign(mname, mk_eq(h_1, h_2));
            } else if (is_abstraction(b)) {
                // Lambdas and Pis
                // Imitation for Lambdas and Pis, b == Fun(x:T) B
                // mname <- Fun (x:?h_1) ?h_2 x)
                expr h_1; // = new_s.mk_metavar(ctx);
                expr h_2; // = new_s.mk_metavar(ctx);
                new_s.assign(mname, update_abstraction(b, h_1, mk_app(h_2, Var(0))));
            } else {
                new_q.push_front(constraint(ctx, pop_meta_context(a), lift_free_vars(b, i, 1)));
            }
            m_state_stack.push_back(mk_state(new_s, new_q));
            reset_delayed();
        }
    }

    /**
       \brief Process the constraint \c c. Return true if the constraint was processed or postponed, and false
       if it failed to solve the constraint.
    */
    bool process(constraint const & c, substitution & s) {
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
        if (m_use_beta) {
            a = head_beta_reduce(a);
            b = head_beta_reduce(b);
        }
        if (is_metavar_inst(a) && (!is_metavar_inst(b) && !is_meta_app(b))) {
            process_metavar_inst(ctx, a, b);
            return true;
        }
        if (is_metavar_inst(b) && (!is_metavar_inst(a) && !is_meta_app(a))) {
            process_metavar_inst(ctx, b, a);
            return true;
        }
        if (is_metavar_with_context(a)  || is_metavar_with_context(b) ||
            is_meta_app_with_context(a) || is_meta_app_with_context(b)) {
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
                return a == b;
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

        if (m_use_normalizer) {
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
        } else {
            if (a.kind() != b.kind())
                return false;
            if (is_app(a)) {
                return process_app_args(ctx, a, b, 0);
            } else if (!is_eqp(a, old_a) || !is_eqp(b, old_b)) {
                // some progress was made
                add_constraint(ctx, a, b);
                return true;
            } else {
                return false;
            }
        }
    }

public:
    imp(environment const & env, options const & opts):
        m_env(env),
        m_normalizer(env, opts),
        m_type_infer(env) {
        m_interrupted       = false;
        m_delayed           = 0;
        m_max_solutions     = get_ho_unifier_max_solutions(opts);
        m_remove_duplicates = get_ho_unifier_remove_duplicates(opts);
        m_use_normalizer    = get_ho_unifier_use_normalizer(opts);
        m_use_beta          = get_ho_unifier_use_beta(opts);
    }

    list<result> unify(context const & ctx, expr const & a, expr const & b, substitution const & subst) {
        init(ctx, a, b, subst);
        list<result> r;
        unsigned num_solutions = 0;
        while (!m_state_stack.empty()) {
            check_interrupted(m_interrupted);
            if (num_solutions > m_max_solutions)
                return r;
            state & top_state = m_state_stack.back();
            cqueue & cq       = queue_of(top_state);
            unsigned cq_size  = cq.size();
            if (cq.empty()) {
                // no constraints left to be solved
                r = save_result(r, subst_of(top_state), residue(), subst);
                num_solutions++;
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
                    r = save_result(r, subst_of(top_state), rs, subst);
                    num_solutions++;
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

ho_unifier::ho_unifier(environment const & env, options const & opts):m_ptr(new imp(env, opts)) {}
ho_unifier::~ho_unifier() {}
void ho_unifier::set_interrupt(bool flag) { m_ptr->set_interrupt(flag); }
list<ho_unifier::result> ho_unifier::operator()(context const & ctx, expr const & l, expr const & r, substitution const & subst) {
    return m_ptr->unify(ctx, l, r, subst);
}
}
