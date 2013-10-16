/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <vector>
#include "util/pdeque.h"
#include "kernel/formatter.h"
#include "library/light_checker.h"
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
    state                                    m_state;
    std::vector<std::unique_ptr<case_split>> m_case_splits;
    std::shared_ptr<synthesizer>             m_synthesizer;
    std::shared_ptr<elaborator_plugin>       m_plugin;
    unsigned                                 m_next_id;
    unsigned                                 m_delayed;
    trace                                    m_conflict;
    bool                                     m_interrupted;


    // options
    bool                                     m_use_traces;
    bool                                     m_use_beta;
    bool                                     m_use_normalizer;

    void set_options(options const &) {
        m_use_traces     = true;
        m_use_beta       = true;
        m_use_normalizer = true;
    }

    void reset_delayed() {
        m_delayed = 0;
    }

    trace mk_assumption() {
        unsigned id = m_next_id;
        m_next_id++;
        return trace(new assumption_trace(id));
    }

    bool process(unification_constraint const & c) {
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

    bool process_eq_convertible(context const & ctx, expr const & from, expr const & to, unification_constraint const & c) {
        bool eq = is_eq(c);
        if (from == to) {
            reset_delayed();
            return true;
        }

        // TODO(Leo)

        if (is_type(from) && is_type(to)) {
            if ((!eq && m_env.is_ge(ty_level(to), ty_level(from))) || (eq && from == to)) {
                reset_delayed();
                return true;
            } else {
                m_conflict = trace(new unification_failure_trace(c));
                return false;
            }
        }

        if (is_pi(from) && is_pi(to)) {
            trace new_trace(new destruct_trace(c));
            m_state.m_queue.push_front(mk_eq_constraint(ctx, abst_domain(from), abst_domain(to), new_trace));
            context new_ctx = extend(ctx, abst_name(from), abst_domain(from));
            if (eq)
                m_state.m_queue.push_front(mk_eq_constraint(new_ctx, abst_body(from), abst_body(to), new_trace));
            else
                m_state.m_queue.push_front(mk_convertible_constraint(new_ctx, abst_body(from), abst_body(to), new_trace));
            reset_delayed();
            return true;
        }


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
                    return;
                }
            }
            m_case_splits.pop_back();
        }
        throw elaborator_exception(m_conflict);
    }

    /**
        \brief Return a unassigned metavariable in the current state.
        Return the anonymous name if the state does not contain unassigned metavariables.
    */
    name find_unassigned_metavar() const {
        return m_state.m_menv.find_unassigned_metavar();
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

    bool next_choice_case(choice_case_split & s) {
        unification_constraint & choice = s.m_choice;
        unsigned idx = s.m_idx;
        if (idx < choice_size(choice)) {
            s.m_idx++;
            s.m_curr_assumption = mk_assumption();
            m_state = s.m_prev_state;
            m_state.m_queue.push_front(mk_eq_constraint(get_context(choice), choice_mvar(choice), choice_ith(choice, idx), s.m_curr_assumption));
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
                m_state.m_queue.push_front(c);
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
        m_state(menv, num_cnstrs, cnstrs),
        m_synthesizer(s),
        m_plugin(p) {
        set_options(opts);
        m_next_id     = 0;
        m_delayed     = 0;
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
        reset_delayed();
        while (true) {
            check_interrupted(m_interrupted);
            cnstr_queue & q = m_state.m_queue;
            if (q.empty()) {
                name m = find_unassigned_metavar();
                if (m) {
                    // TODO(Leo)
                    // erase the following line, and implement interface with synthesizer
                    return m_state.m_menv.get_substitutions();
                } else {
                    return m_state.m_menv.get_substitutions();
                }
            } else {
                unification_constraint c = q.front();
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
    }

    void display(std::ostream & out) const {
        m_state.m_menv.get_substitutions().for_each([&](name const & m, expr const & e) {
                out << m << " <- " << e << "\n";
            });
        formatter fmt = mk_simple_formatter();
        for (auto c : m_state.m_queue) {
            out << c.pp(fmt, options(), nullptr, false) << "\n";
        }
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
