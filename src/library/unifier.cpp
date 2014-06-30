/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <memory>
#include <vector>
#include "util/interrupt.h"
#include "util/luaref.h"
#include "util/lazy_list_fn.h"
#include "util/sstream.h"
#include "util/lbool.h"
#include "kernel/for_each_fn.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "library/occurs.h"
#include "library/unifier.h"
#include "library/kernel_bindings.h"

namespace lean {
static name g_unifier_max_steps      {"unifier", "max_steps"};
RegisterUnsignedOption(g_unifier_max_steps, LEAN_DEFAULT_UNIFIER_MAX_STEPS, "(unifier) maximum number of steps");
static name g_unifier_use_exceptions {"unifier", "use_exceptions"};
RegisterBoolOption(g_unifier_use_exceptions, true, "(unifier) throw an exception when there are no more solutions");
unsigned get_unifier_max_steps(options const & opts) {
    return opts.get_unsigned(g_unifier_max_steps, LEAN_DEFAULT_UNIFIER_MAX_STEPS);
}
bool get_unifier_use_exceptions(options const & opts) {
    return opts.get_bool(g_unifier_use_exceptions, true);
}

// If \c e is a metavariable ?m or a term of the form (?m l_1 ... l_n) where
// l_1 ... l_n are distinct local variables, then return ?m, and store l_1 ... l_n in args.
// Otherwise return none.
optional<expr> is_simple_meta(expr const & e, buffer<expr> & args) {
    expr const & m = get_app_args(e, args);
    if (!is_metavar(m))
        return none_expr();
    for (auto it = args.begin(); it != args.end(); it++) {
        if (!is_local(*it) || std::find(args.begin(), it, *it) != it)
            return none_expr();
    }
    return some_expr(m);
}

bool is_simple_meta(expr const & e) {
    buffer<expr> args;
    return (bool)is_simple_meta(e, args); // NOLINT
}

// Return true if all local constants in \c e are in locals
bool context_check(expr const & e, buffer<expr> const & locals) {
    bool failed = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (failed)
                return false;
            if (is_local(e) && std::find(locals.begin(), locals.end(), e) == locals.end()) {
                failed = true;
                return false;
            }
            return true;
        });
    return !failed;
}

// Return
//   - l_undef if \c e contains a metavariable application that contains
//     a local constant not in locals
//   - l_true if \c e does not contain the metavariable \c m, and all local
//     constants are in \c e are in \c locals.
//   - l_false if \c e contains \c m or it contains a local constant \c l
//     not in locals that is not in a metavariable application.
lbool occurs_context_check(expr const & e, expr const & m, buffer<expr> const & locals) {
    expr root = e;
    lbool r = l_true;
    for_each(e, [&](expr const & e, unsigned) {
            if (r == l_false) {
                return false;
            } else if (is_local(e) && std::find(locals.begin(), locals.end(), e) == locals.end()) {
                // right-hand-side contains variable that is not in the scope
                // of metavariable.
                r = l_false;
                return false;
            } else if (is_meta(e)) {
                if (!context_check(e, locals) || occurs(m, e))
                    r = l_undef;
                if (get_app_fn(e) == m)
                    r = l_false;
                return false; // do not visit children
            } else {
                // we only need to continue exploring e if it contains
                // metavariables and/or local constants.
                return has_metavar(e) || has_local(e);
            }
        });
    return r;
}

// Create a lambda abstraction by abstracting the local constants \c locals in \c e
expr lambda_abstract_locals(expr const & e, buffer<expr> const & locals) {
    expr v = abstract_locals(e, locals.size(), locals.data());
    unsigned i = locals.size();
    while (i > 0) {
        --i;
        expr t = abstract_locals(mlocal_type(locals[i]), i, locals.data());
        v = mk_lambda(local_pp_name(locals[i]), t, v);
    }
    return v;
}

static std::pair<unify_status, substitution> unify_simple_core(substitution const & s, expr const & lhs, expr const & rhs,
                                                               justification const & j) {
    lean_assert(is_meta(lhs));
    buffer<expr> args;
    auto m = is_simple_meta(lhs, args);
    if (!m || is_meta(rhs)) {
        return mk_pair(unify_status::Unsupported, s);
    } else {
        switch (occurs_context_check(rhs, *m, args)) {
        case l_false: return mk_pair(unify_status::Failed, s);
        case l_undef: mk_pair(unify_status::Unsupported, s);
        case l_true: {
            expr v = lambda_abstract_locals(rhs, args);
            return mk_pair(unify_status::Solved, s.assign(mlocal_name(*m), v, j));
        }}
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

std::pair<unify_status, substitution> unify_simple(substitution const & s, expr const & lhs, expr const & rhs, justification const & j) {
    if (lhs == rhs)
        return mk_pair(unify_status::Solved, s);
    else if (!has_metavar(lhs) && !has_metavar(rhs))
        return mk_pair(unify_status::Failed, s);
    else if (is_meta(lhs))
        return unify_simple_core(s, lhs, rhs, j);
    else if (is_meta(rhs))
        return unify_simple_core(s, rhs, lhs, j);
    else
        return mk_pair(unify_status::Unsupported, s);
}

// Return true if m occurs in e
bool occurs_meta(level const & m, level const & e) {
    lean_assert(is_meta(m));
    bool contains = false;
    for_each(e, [&](level const & l) {
            if (contains)
                return false;
            if (l == m) {
                contains = true;
                return false;
            }
            return has_meta(l);
        });
    return contains;
}

std::pair<unify_status, substitution> unify_simple_core(substitution const & s, level const & lhs, level const & rhs, justification const & j) {
    lean_assert(is_meta(lhs));
    bool contains = occurs_meta(lhs, rhs);
    if (contains) {
        if (is_succ(rhs))
            return mk_pair(unify_status::Failed, s);
        else
            return mk_pair(unify_status::Unsupported, s);
    }
    return mk_pair(unify_status::Solved, s.assign(meta_id(lhs), rhs, j));
}

std::pair<unify_status, substitution> unify_simple(substitution const & s, level const & lhs, level const & rhs, justification const & j) {
    if (lhs == rhs)
        return mk_pair(unify_status::Solved, s);
    else if (!has_meta(lhs) && !has_meta(rhs))
        return mk_pair(unify_status::Failed, s);
    else if (is_meta(lhs))
        return unify_simple_core(s, lhs, rhs, j);
    else if (is_meta(rhs))
        return unify_simple_core(s, rhs, lhs, j);
    else if (is_succ(lhs) && is_succ(rhs))
        return unify_simple(s, succ_of(lhs), succ_of(rhs), j);
    else
        return mk_pair(unify_status::Unsupported, s);
}

std::pair<unify_status, substitution> unify_simple(substitution const & s, constraint const & c) {
    if (is_eq_cnstr(c))
        return unify_simple(s, cnstr_lhs_expr(c), cnstr_rhs_expr(c), c.get_justification());
    else if (is_level_eq_cnstr(c))
        return unify_simple(s, cnstr_lhs_level(c), cnstr_rhs_level(c), c.get_justification());
    else
        return mk_pair(unify_status::Unsupported, s);
}

static constraint g_dont_care_cnstr = mk_eq_cnstr(expr(), expr(), justification());
static unsigned g_first_delayed      = 1u << 28;
static unsigned g_first_very_delayed = 1u << 30;

/** \brief Auxiliary functional object for implementing simultaneous higher-order unification */
struct unifier_fn {
    typedef std::pair<constraint, unsigned> cnstr; // constraint + idx
    struct cnstr_cmp {
        int operator()(cnstr const & c1, cnstr const & c2) const { return c1.second < c2.second ? -1 : (c1.second == c2.second ? 0 : 1); }
    };
    typedef rb_tree<cnstr, cnstr_cmp> cnstr_set;
    typedef rb_tree<unsigned, unsigned_cmp> cnstr_idx_set;
    typedef rb_map<name, cnstr_idx_set, name_quick_cmp> name_to_cnstrs;

    environment      m_env;
    name_generator   m_ngen;
    substitution     m_subst;
    unifier_plugin   m_plugin;
    type_checker     m_tc;
    bool             m_use_exception; //!< True if we should throw an exception when there are no more solutions.
    unsigned         m_max_steps;
    unsigned         m_num_steps;
    bool             m_first; //!< True if we still have to generate the first solution.
    unsigned         m_next_assumption_idx; //!< Next assumption index.
    unsigned         m_next_cidx; //!< Next constraint index.
    /**
       \brief "Queue" of constraints to be solved.

       We implement it using a red-black-tree because:
       1- Our red-black-trees support a O(1) copy operation. So, it is cheap to create a snapshot
       whenever we create a backtracking point.

       2- We can easily remove any constraint from the queue in O(n log n). We do that when
       a metavariable \c m is assigned, and we want to instantiate it in all constraints that
       contains it.
    */
    cnstr_set        m_cnstrs;
    /**
        \brief The following two maps are indices. The map a metavariable name \c m to the se of all constraint indices that contain \c m.
        We use these indices whenever a metavariable \c m is assigned. In this case, we used these indices to
        remove any constraint that contains \c m from \c m_cnstrs, instantiate \c m, and reprocess them.

        \remark \c m_mvar_occs is for regular metavariables, and \c m_mlvl_occs is for universe metavariables.
    */
    name_to_cnstrs   m_mvar_occs;
    name_to_cnstrs   m_mlvl_occs;

    /**
        \brief Base class for the case-splits created by the unifier.

        We have three different kinds of case splits:
        1- unifier plugin
        2- choice constraints
        3- higher-order unification
    */
    struct case_split {
        unsigned         m_assumption_idx; // idx of the current assumption
        justification    m_failed_justifications; // justifications for failed branches
        // snapshot of unifier's state
        substitution     m_subst;
        cnstr_set        m_cnstrs;
        name_to_cnstrs   m_mvar_occs;
        name_to_cnstrs   m_mlvl_occs;

        /** \brief Save unifier's state */
        case_split(unifier_fn & u):
            m_assumption_idx(u.m_next_assumption_idx), m_subst(u.m_subst), m_cnstrs(u.m_cnstrs),
            m_mvar_occs(u.m_mvar_occs), m_mlvl_occs(u.m_mlvl_occs) {
            u.m_next_assumption_idx++;
            u.m_tc.push();
        }

        /** \brief Restore unifier's state with saved values, and update m_assumption_idx and m_failed_justifications. */
        void restore_state(unifier_fn & u) {
            lean_assert(u.in_conflict());
            u.m_tc.pop();   // restore type checker state
            u.m_tc.push();
            u.m_subst     = m_subst;
            u.m_cnstrs    = m_cnstrs;
            u.m_mvar_occs = m_mvar_occs;
            u.m_mlvl_occs = m_mlvl_occs;
            m_assumption_idx = u.m_next_assumption_idx;
            m_failed_justifications = mk_composite1(m_failed_justifications, *u.m_conflict);
            u.m_next_assumption_idx++;
            u.m_conflict  = optional<justification>();
        }

        virtual ~case_split() {}
        virtual bool next(unifier_fn & u) = 0;
    };
    typedef std::vector<std::unique_ptr<case_split>> case_split_stack;

    struct plugin_case_split : public case_split {
        lazy_list<constraints> m_tail;
        plugin_case_split(unifier_fn & u, lazy_list<constraints> const & tail):case_split(u), m_tail(tail) {}
        virtual bool next(unifier_fn & u) { return u.next_plugin_case_split(*this); }
    };

    struct choice_case_split : public case_split {
        expr                 m_expr;
        justification        m_jst;
        lazy_list<a_choice>  m_tail;
        choice_case_split(unifier_fn & u, expr const & expr, justification const & j, lazy_list<a_choice> const & tail):
            case_split(u), m_expr(expr), m_jst(j), m_tail(tail) {}
        virtual bool next(unifier_fn & u) { return u.next_choice_case_split(*this); }
    };

    struct ho_case_split : public case_split {
        list<constraints> m_tail;
        ho_case_split(unifier_fn & u, list<constraints> const & tail):case_split(u), m_tail(tail) {}
        virtual bool next(unifier_fn & u) { return u.next_ho_case_split(*this); }
    };

    case_split_stack        m_case_splits;
    optional<justification> m_conflict; //!< if different from none, then there is a conflict.

    unifier_fn(environment const & env, unsigned num_cs, constraint const * cs,
               name_generator const & ngen, substitution const & s, unifier_plugin const & p,
               bool use_exception, unsigned max_steps):
        m_env(env), m_ngen(ngen), m_subst(s), m_plugin(p),
        m_tc(env, m_ngen.mk_child()),
        m_use_exception(use_exception), m_max_steps(max_steps), m_num_steps(0) {
        m_next_assumption_idx = 0;
        m_next_cidx = 0;
        m_first     = true;
        for (unsigned i = 0; i < num_cs; i++) {
            process_constraint(cs[i]);
        }
    }

    void check_system() {
        check_interrupted();
        if (m_num_steps > m_max_steps)
            throw exception(sstream() << "unifier maximum number of steps (" << m_max_steps << ") exceeded, " <<
                            "the maximum number of steps can be increased by setting the option unifier.max_steps " <<
                            "(remark: the unifier uses higher order unification and unification-hints, which may trigger non-termination");
        m_num_steps++;
    }

    bool in_conflict() const { return (bool)m_conflict; } // NOLINT
    void set_conflict(justification const & j) { m_conflict = j; }
    void update_conflict(justification const & j) { m_conflict = j; }
    void reset_conflict() { m_conflict = optional<justification>(); lean_assert(!in_conflict()); }

    /** \brief Given \c type of the form <tt>(Pi ctx, r)</tt>, return <tt>(Pi ctx, new_range)</tt> */
    static expr replace_range(expr const & type, expr const & new_range) {
        if (is_pi(type))
            return update_binding(type, binding_domain(type), replace_range(binding_body(type), new_range));
        else
            return new_range;
    }

    /** \brief Return the "arity" of the given type. The arity is the number of nested pi-expressions. */
    static unsigned get_arity(expr type) {
        unsigned r = 0;
        while (is_pi(type)) {
            type = binding_body(type);
            r++;
        }
        return r;
    }

    /** \brief Return the term (f #n-1 ... #0) */
    static expr mk_app_vars(expr const & f, unsigned n) {
        expr r     = f;
        unsigned i = n;
        while (i > 0) {
            --i;
            r = r(mk_var(i));
        }
        return r;
    }

    /**
       \brief Given a type \c t of the form
           <tt>Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), B[x_1, ..., x_n]</tt>
       return a new metavariable \c m1 with type
           <tt>Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{u}</tt>
       where \c u is a new universe metavariable.
    */
    expr mk_aux_type_metavar_for(expr const & t) {
        expr new_type = replace_range(t, mk_sort(mk_meta_univ(m_ngen.next())));
        name n        = m_ngen.next();
        return mk_metavar(n, new_type);
    }

    /**
       \brief Given a type \c t of the form
           <tt>Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), B[x_1, ..., x_n]</tt>
       return a new metavariable \c m1 with type
           <tt>Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), (m2 x_1 ... x_n)</tt>
       where \c m2 is a new metavariable with type
           <tt>Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{u}</tt>
       where \c u is a new universe metavariable.
    */
    expr mk_aux_metavar_for(expr const & t) {
        unsigned num  = get_arity(t);
        expr r        = mk_app_vars(mk_aux_type_metavar_for(t), num);
        expr new_type = replace_range(t, r);
        name n        = m_ngen.next();
        return mk_metavar(n, new_type);
    }

    /**
       \brief Given t
           <tt>Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), B[x_1, ..., x_n]</tt>
       return
           <tt>fun (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), v</tt>
    */
    expr mk_lambda_for(expr const & t, expr const & v) {
        if (is_pi(t)) {
            return mk_lambda(binding_name(t), binding_domain(t), mk_lambda_for(binding_body(t), v), binding_info(t));
        } else {
            return v;
        }
    }

    /**
        \brief Update occurrence index with entry <tt>m -> cidx</tt>, where \c m is the name of a metavariable,
        and \c cidx is the index of a constraint that contains \c m.

        \remark \c MVar is true if \c m is a regular metavariable, and false if it is a universe metavariable.
    */
    template<bool MVar>
    void add_occ(name const & m, unsigned cidx) {
        cnstr_idx_set s;
        name_to_cnstrs & map = MVar ? m_mvar_occs : m_mlvl_occs;
        auto it = map.find(m);
        if (it)
            s = *it;
        if (!s.contains(cidx)) {
            s.insert(cidx);
            map.insert(m, s);
        }
    }

    /** \see add_occ */
    void add_mvar_occ(name const & m, unsigned cidx) { add_occ<true>(m, cidx); }
    /** \see add_occ */
    void add_mlvl_occ(name const & m, unsigned cidx) { add_occ<false>(m, cidx); }

    /**
        \brief Update the indices \c m_mvar_occs and \c m_mlvl_occs.
        For every metavariable name \c m in \c mlvl_occs and \c mvar_occs, add an entry to \c cidx.

        \remark \c cidx is the index of some constraint in \c m_cnstrs.
    */
    void add_occs(unsigned cidx, name_set const * mlvl_occs, name_set const * mvar_occs) {
        if (mlvl_occs) {
            mlvl_occs->for_each([=](name const & m) {
                    add_mlvl_occ(m, cidx);
                });
        }
        if (mvar_occs) {
            mvar_occs->for_each([=](name const & m) {
                    add_mvar_occ(m, cidx);
                });
        }
    }

    /** \brief Add constraint to the constraint queue */
    void add_cnstr(constraint const & c, name_set const * mlvl_occs, name_set const * mvar_occs, unsigned start_cidx = 0) {
        unsigned cidx = m_next_cidx + start_cidx;
        m_cnstrs.insert(cnstr(c, cidx));
        add_occs(cidx, mlvl_occs, mvar_occs);
        m_next_cidx++;
    }

    /**
        \brief Add (delayed) constraint to the constraint queue. Delayed constraints are processed after regular constraints
        added with \c add_cnstr
    */
    void add_delayed_cnstr(constraint const & c, name_set const * mlvl_occs, name_set const * mvar_occs) {
        add_cnstr(c, mlvl_occs, mvar_occs, g_first_delayed);
    }

    /**
       \brief Add (very delayed) constraint to the constraint queue. Very delayed constraints are processed after
       regular and delayed constraints added with \c add_cnstr and \c add_delayed_cnstr.
    */
    void add_very_delayed_cnstr(constraint const & c, name_set const * mlvl_occs, name_set const * mvar_occs) {
        add_cnstr(c, mlvl_occs, mvar_occs, g_first_very_delayed);
    }

    /**
       \brief Assign \c v to metavariable \c m with justification \c j.
       The type of v and m are inferred, and is_def_eq is invoked.
       Any constraint that contains \c m is revisited.
    */
    bool assign(expr const & m, expr const & v, justification const & j) {
        lean_assert(is_metavar(m));
        m_subst = m_subst.assign(m, v, j);
        expr m_type = mlocal_type(m);
        expr v_type = m_tc.infer(v);
        if (in_conflict())
            return false;
        if (!m_tc.is_def_eq(m_type, v_type, j)) {
            set_conflict(j);
            return false;
        }
        auto it = m_mvar_occs.find(mlocal_name(m));
        if (it) {
            cnstr_idx_set s = *it;
            m_mvar_occs.erase(mlocal_name(m));
            s.for_each([&](unsigned cidx) {
                    process_constraint_cidx(cidx);
                });
            return !in_conflict();
        } else {
            return true;
        }
    }

    /**
       \brief Assign \c v to universe metavariable \c m with justification \c j.
       Any constraint that contains \c m is revisted.
    */
    bool assign(level const & m, level const & v, justification const & j) {
        lean_assert(is_meta(m));
        m_subst = m_subst.assign(m, v, j);
        auto it = m_mlvl_occs.find(meta_id(m));
        if (it) {
            cnstr_idx_set s = *it;
            m_mlvl_occs.erase(meta_id(m));
            s.for_each([&](unsigned cidx) {
                    process_constraint_cidx(cidx);
                });
            return !in_conflict();
        } else {
            return true;
        }
    }

    enum status { Assigned, Failed, Continue };
    /**
       \brief Process constraints of the form <tt>lhs =?= rhs</tt> where lhs is of the form <tt>?m</tt> or <tt>(?m l_1 .... l_n)</tt>,
       where all \c l_i are distinct local variables. In this case, the method returns Assigned, if the method assign succeeds.
       The method returns \c Failed if \c rhs contains <tt>?m</tt>, or it contains a local constant not in <tt>{l_1, ..., l_n}</tt>.
       Otherwise, it returns \c Continue.
    */
    status process_metavar_eq(expr const & lhs, expr const & rhs, justification const & j) {
        if (!is_meta(lhs))
            return Continue;
        buffer<expr> locals;
        auto m = is_simple_meta(lhs, locals);
        if (!m || is_meta(rhs))
            return Continue;
        switch (occurs_context_check(rhs, *m, locals)) {
        case l_false:
            set_conflict(j);
            return Failed;
        case l_undef:
            return Continue;
        case l_true:
            lean_assert(!m_subst.is_assigned(*m));
            if (assign(*m, lambda_abstract_locals(rhs, locals), j)) {
                return Assigned;
            } else {
                return Failed;
            }
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    /** \brief Process an equality constraints. */
    bool process_eq_constraint(constraint const & c) {
        lean_assert(is_eq_cnstr(c));
        // instantiate assigned metavariables
        name_set unassigned_lvls, unassigned_exprs;
        auto lhs_jst = m_subst.instantiate_metavars(cnstr_lhs_expr(c), &unassigned_lvls, &unassigned_exprs);
        auto rhs_jst = m_subst.instantiate_metavars(cnstr_rhs_expr(c), &unassigned_lvls, &unassigned_exprs);
        expr lhs = lhs_jst.first;
        expr rhs = rhs_jst.first;

        if (lhs == rhs)
            return true; // trivial constraint

        // Update justification using the justification of the instantiated metavariables
        justification new_jst = mk_composite1(mk_composite1(c.get_justification(), lhs_jst.second), rhs_jst.second);
        if (!has_metavar(lhs) && !has_metavar(rhs)) {
            set_conflict(new_jst);
            return false; // trivial failure
        }

        // Handle higher-order pattern matching.
        status st = process_metavar_eq(lhs, rhs, new_jst);
        if (st != Continue) return st == Assigned;
        st = process_metavar_eq(rhs, lhs, new_jst);
        if (st != Continue) return st == Assigned;

        // Make sure lhs/rhs are in weak-head-normal-form
        rhs = m_tc.whnf(rhs);
        lhs = m_tc.whnf(lhs);

        // If lhs or rhs were updated, then invoke is_def_eq again.
        if (lhs != cnstr_lhs_expr(c) || rhs != cnstr_rhs_expr(c)) {
            // some metavariables were instantiated, try is_def_eq again
            if (m_tc.is_def_eq(lhs, rhs, new_jst)) {
                return true;
            } else {
                set_conflict(new_jst);
                return false;
            }
        }

        if (is_meta(lhs) && is_meta(rhs)) {
            // flex-flex constraints are delayed the most.
            add_very_delayed_cnstr(c, &unassigned_lvls, &unassigned_exprs);
        } else if (is_meta(lhs) || is_meta(rhs)) {
            // flex-rigid constraints are delayed.
            add_delayed_cnstr(c, &unassigned_lvls, &unassigned_exprs);
        } else {
            // this constraints require the unifier plugin to be solved
            add_cnstr(c, &unassigned_lvls, &unassigned_exprs);
        }
        return true;
    }

    /**
       \brief Process a universe level constraints of the form <tt>?m =?= rhs</tt>. It fails if rhs contains \c ?m and
       is definitely bigger than \c ?m.

       TODO(Leo): we should improve this method in the future. It is doing only very basic things.
    */
    status process_metavar_eq(level const & lhs, level const & rhs, justification const & j) {
        if (!is_meta(lhs))
            return Continue;
        bool contains = occurs_meta(lhs, rhs);
        if (contains) {
            if (is_succ(rhs))
                return Failed;
            else
                return Continue;
        }
        lean_assert(!m_subst.is_assigned(lhs));
        if (assign(lhs, rhs, j)) {
            return Assigned;
        } else {
            return Failed;
        }
    }

    /** \brief Process a universe level contraints. */
    bool process_level_eq_constraint(constraint const & c) {
        lean_assert(is_level_eq_cnstr(c));
        // instantiate assigned metavariables
        name_set unassigned_lvls;
        auto lhs_jst = m_subst.instantiate_metavars(cnstr_lhs_level(c), &unassigned_lvls);
        auto rhs_jst = m_subst.instantiate_metavars(cnstr_rhs_level(c), &unassigned_lvls);
        level lhs = lhs_jst.first;
        level rhs = rhs_jst.first;

        // normalize lhs and rhs
        lhs = normalize(lhs);
        rhs = normalize(rhs);
        // eliminate outermost succs
        while (is_succ(lhs) && is_succ(rhs)) {
            lhs = succ_of(lhs);
            rhs = succ_of(rhs);
        }

        if (lhs == rhs)
            return true; // trivial constraint

        justification new_jst = mk_composite1(mk_composite1(c.get_justification(), lhs_jst.second), rhs_jst.second);
        if (!has_meta(lhs) && !has_meta(rhs)) {
            set_conflict(new_jst);
            return false; // trivial failure
        }

        status st = process_metavar_eq(lhs, rhs, new_jst);
        if (st != Continue) return st == Assigned;
        st = process_metavar_eq(rhs, lhs, new_jst);
        if (st != Continue) return st == Assigned;

        if (lhs != cnstr_lhs_level(c) || rhs != cnstr_rhs_level(c)) {
            constraint new_c = mk_level_eq_cnstr(lhs, rhs, new_jst);
            add_delayed_cnstr(new_c, &unassigned_lvls, nullptr);
        } else {
            add_delayed_cnstr(c, &unassigned_lvls, nullptr);
        }

        return true;
    }

    /**
        \brief Process the given constraint \c c. "Easy" constraints are solved, and the remaining ones
        are added to the constraint queue m_cnstrs. By "easy", see the methods
        #process_eq_constraint and #process_level_eq_constraint.
    */
    bool process_constraint(constraint const & c) {
        if (in_conflict())
            return false;
        check_system();
        switch (c.kind()) {
        case constraint_kind::Choice:
            // Choice constraints are never considered easy.
            if (cnstr_delayed(c))
                add_very_delayed_cnstr(c, nullptr, nullptr);
            else
                add_cnstr(c, nullptr, nullptr);
            return true;
        case constraint_kind::Eq:
            return process_eq_constraint(c);
        case constraint_kind::LevelEq:
            return process_level_eq_constraint(c);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    /**
       \brief Process constraint with index \c cidx. The constraint is removed
       from the constraint queue, and the method #process_constraint is invoked.
    */
    bool process_constraint_cidx(unsigned cidx) {
        if (in_conflict())
            return false;
        cnstr c(g_dont_care_cnstr, cidx);
        if (auto it = m_cnstrs.find(c)) {
            constraint c2 = it->first;
            m_cnstrs.erase(c);
            return process_constraint(c2);
        }
        return true;
    }

    void add_case_split(std::unique_ptr<case_split> && cs) {
        m_case_splits.push_back(std::move(cs));
    }

    // This method is used only for debugging purposes.
    void display(std::ostream & out, justification const & j, unsigned indent = 0) {
        for (unsigned i = 0; i < indent; i++)
            out << " ";
        out << j.pp(mk_simple_formatter(), options(), nullptr, m_subst) << "\n";
        if (j.is_composite()) {
            display(out, composite_child1(j), indent+2);
            display(out, composite_child2(j), indent+2);
        }
    }

    bool resolve_conflict() {
        lean_assert(in_conflict());
        // Remark: we must save the value of m_conflict because d->next(*this) may change it.
        justification conflict = *m_conflict;
        while (!m_case_splits.empty()) {
            std::unique_ptr<case_split> & d = m_case_splits.back();
            if (depends_on(conflict, d->m_assumption_idx)) {
                d->m_failed_justifications = mk_composite1(d->m_failed_justifications, conflict);
                if (d->next(*this)) {
                    reset_conflict();
                    return true;
                }
            }
            m_tc.pop();
            m_case_splits.pop_back();
        }
        return false;
    }

    optional<substitution> failure() {
        lean_assert(in_conflict());
        if (m_use_exception)
            throw unifier_exception(*m_conflict, m_subst);
        else
            return optional<substitution>();
    }

    /** \brief Process constraints in \c cs, and append justification \c j to them. */
    bool process_constraints(constraints const & cs, justification const & j) {
        for (constraint const & c : cs)
            process_constraint(update_justification(c, mk_composite1(c.get_justification(), j)));
        return !in_conflict();
    }

    bool process_choice_result(expr const & m, a_choice const & r, justification j) {
        j = mk_composite1(j, std::get<1>(r));
        return
            process_constraint(mk_eq_cnstr(m, std::get<0>(r), j)) &&
            process_constraints(std::get<2>(r), j);
    }

    bool next_choice_case_split(choice_case_split & cs) {
        auto r = cs.m_tail.pull();
        if (r) {
            cs.restore_state(*this);
            lean_assert(!in_conflict());
            cs.m_tail = r->second;
            justification a = mk_assumption_justification(cs.m_assumption_idx);
            return process_choice_result(cs.m_expr, r->first, mk_composite1(cs.m_jst, a));
        } else {
            // update conflict
            update_conflict(mk_composite1(*m_conflict, cs.m_failed_justifications));
            return false;
        }
    }

    bool process_choice_constraint(constraint const & c) {
        lean_assert(is_choice_cnstr(c));
        expr const &   m     = cnstr_expr(c);
        choice_fn const & fn = cnstr_choice_fn(c);
        auto m_type_jst      = m_subst.instantiate_metavars(m_tc.infer(m), nullptr, nullptr);
        auto rlist           = fn(m_type_jst.first, m_subst, m_ngen.mk_child());
        auto r               = rlist.pull();
        justification j      = mk_composite1(c.get_justification(), m_type_jst.second);
        if (r) {
            if (r->second.is_nil()) {
                // there is only one alternative
                return process_choice_result(m, r->first, j);
            } else {
                justification a = mk_assumption_justification(m_next_assumption_idx);
                add_case_split(std::unique_ptr<case_split>(new choice_case_split(*this, m, m_type_jst.second, r->second)));
                return process_choice_result(m, r->first, mk_composite1(j, a));
            }
        } else {
            set_conflict(j);
            return false;
        }
    }

    bool next_plugin_case_split(plugin_case_split & cs) {
        auto r = cs.m_tail.pull();
        if (r) {
            cs.restore_state(*this);
            lean_assert(!in_conflict());
            cs.m_tail = r->second;
            return process_constraints(r->first, mk_assumption_justification(cs.m_assumption_idx));
        } else {
            // update conflict
            update_conflict(mk_composite1(*m_conflict, cs.m_failed_justifications));
            return false;
        }
    }

    bool process_plugin_constraint(constraint const & c) {
        lean_assert(!is_choice_cnstr(c));
        lazy_list<constraints> alts = m_plugin(c, m_ngen.mk_child());
        auto r = alts.pull();
        if (!r) {
            set_conflict(c.get_justification());
            return false;
        } else {
            // create a backtracking point
            justification a = mk_assumption_justification(m_next_assumption_idx);
            add_case_split(std::unique_ptr<case_split>(new plugin_case_split(*this, r->second)));
            return process_constraints(r->first, a);
        }
    }

    bool next_ho_case_split(ho_case_split & cs) {
        if (!is_nil(cs.m_tail)) {
            cs.restore_state(*this);
            lean_assert(!in_conflict());
            constraints c = head(cs.m_tail);
            cs.m_tail     = tail(cs.m_tail);
            return process_constraints(c, mk_assumption_justification(cs.m_assumption_idx));
        } else {
            // update conflict
            update_conflict(mk_composite1(*m_conflict, cs.m_failed_justifications));
            return false;
        }
    }

    /** \brief Return true iff \c c is a flex-rigid constraint. */
    static bool is_flex_rigid(constraint const & c) {
        if (!is_eq_cnstr(c))
            return false;
        bool is_lhs_meta = is_meta(cnstr_lhs_expr(c));
        bool is_rhs_meta = is_meta(cnstr_rhs_expr(c));
        return is_lhs_meta != is_rhs_meta;
    }

    /** \brief Return true iff \c c is a flex-flex constraint */
    static bool is_flex_flex(constraint const & c) {
        return is_eq_cnstr(c) && is_meta(cnstr_lhs_expr(c)) && is_meta(cnstr_rhs_expr(c));
    }

    /**
       \brief Given
               m      := a metavariable ?m
               margs  := [a_1 ... a_k]
               rhs    := (g b_1 ... b_n)
       Then create the constraints
               (?m_1 a_1 ... a_k) =?= b_1
               ...
               (?m_n a_1 ... a_k) =?= b_n
               ?m  =?= fun (x_1 ... x_k), f (?m_1 x_1 ... x_k) ... (?m_n x_1 ... x_k)

       Remark: The term f is:
                  - g (if g is a constant), OR
                  - variable (if g is a local constant equal to a_i)
    */
    constraints mk_flex_rigid_app_cnstrs(expr const & m, buffer<expr> const & margs,
                                         expr const & f, expr const & rhs, justification const & j) {
        lean_assert(is_metavar(m));
        lean_assert(is_app(rhs));
        lean_assert(is_constant(f) || is_var(f));
        buffer<constraint> cs;
        expr const & mtype = mlocal_type(m);
        buffer<expr> rargs;
        get_app_args(rhs, rargs);
        buffer<expr> sargs;
        for (expr const & rarg : rargs) {
            expr maux = mk_aux_metavar_for(mtype);
            cs.push_back(mk_eq_cnstr(mk_app(maux, margs), rarg, j));
            sargs.push_back(mk_app_vars(maux, margs.size()));
        }
        expr v = mk_app(f, sargs);
        v = mk_lambda_for(mtype, v);
        cs.push_back(mk_eq_cnstr(m, v, j));
        return to_list(cs.begin(), cs.end());
    }

    /**
       \brief Given
               m      := a metavariable ?m
               margs  := [a_1 ... a_k]
               rhs    := (fun/Pi (y : A), B y)
       Then create the constraints
              (?m_1 a_1 ... a_k)   =?= A
              (?m_2 a_1 ... a_k l) =?= B l
              ?m   =?= fun (x_1 ... x_k), fun/Pi (y : ?m_1 x_1 ... x_k), ?m_2 x_1 ... x_k y
       where l is a fresh local constant.
    */
    constraints mk_bindings_imitation(expr const & m, buffer<expr> const & margs, expr const & rhs, justification const & j) {
        lean_assert(is_metavar(m));
        lean_assert(is_binding(rhs));
        expr const & mtype = mlocal_type(m);
        expr maux1  = mk_aux_metavar_for(mtype);
        buffer<constraint> cs;
        cs.push_back(mk_eq_cnstr(mk_app(maux1, margs), binding_domain(rhs), j));
        expr dontcare;
        expr tmp_pi = mk_pi(binding_name(rhs), mk_app_vars(maux1, margs.size()), dontcare); // trick for "extending" the context
        expr mtype2 = replace_range(mtype, tmp_pi); // trick for "extending" the context
        expr maux2  = mk_aux_metavar_for(mtype2);
        expr new_local = mk_local(m_ngen.next(), binding_name(rhs), binding_domain(rhs));
        cs.push_back(mk_eq_cnstr(mk_app(mk_app(maux2, margs), new_local), instantiate(binding_body(rhs), new_local), j));
        expr v = update_binding(rhs, mk_app_vars(maux1, margs.size()), mk_app_vars(maux2, margs.size() + 1));
        v = mk_lambda_for(mtype, v);
        cs.push_back(mk_eq_cnstr(m, v, j));
        return to_list(cs.begin(), cs.end());
    }

    /**
       \brief Given
                 m      := a metavariable ?m
                 rhs    := sort, constant
        Then solve (?m a_1 ... a_k) =?= rhs, by returning the constraint
                 ?m  =?= fun (x1 ... x_k), rhs
    */
    constraints mk_simple_imitation(expr const & m, expr const & rhs, justification const & j) {
        lean_assert(is_metavar(m));
        lean_assert(is_sort(rhs) || is_constant(rhs));
        expr const & mtype = mlocal_type(m);
        expr v = mk_lambda_for(mtype, rhs);
        return constraints(mk_eq_cnstr(m, v, j));
    }

    /**
       \brief Given
               m      := a metavariable ?m
               margs  := [a_1 ... a_k]
               rhs    := M(b_1 ... b_n) where M is a macro with arguments b_1 ... b_n
       Then create the constraints
               (?m_1 a_1 ... a_k) =?= b_1
               ...
               (?m_n a_1 ... a_k) =?= b_n
               ?m  =?= fun (x_1 ... x_k), M((?m_1 x_1 ... x_k) ... (?m_n x_1 ... x_k))
    */
    constraints mk_macro_imitation(expr const & m, buffer<expr> const & margs, expr const & rhs, justification const & j) {
        lean_assert(is_metavar(m));
        lean_assert(is_macro(rhs));
        expr const & mtype = mlocal_type(m);
        buffer<constraint> cs;
        // create an auxiliary metavariable for each macro argument
        buffer<expr> sargs;
        for (unsigned i = 0; i < macro_num_args(rhs); i++) {
            expr maux = mk_aux_metavar_for(mtype);
            cs.push_back(mk_eq_cnstr(mk_app(maux, margs), macro_arg(rhs, i), j));
            sargs.push_back(mk_app_vars(maux, margs.size()));
        }
        expr v = mk_macro(macro_def(rhs), sargs.size(), sargs.data());
        v = mk_lambda_for(mtype, v);
        cs.push_back(mk_eq_cnstr(m, v, j));
        return to_list(cs.begin(), cs.end());
    }

    /**
       Given,
               m      := a metavariable ?m
               margs  := [a_1 ... a_k]
       We say a unification problem (?m a_1 ... a_k) =?= rhs uses "simple projections" IF
       rhs is NOT an application.

       If rhs is a local constant and a_i == rhs, then we add the constraint
                ?m =?= fun x_1 ... x_k, x_i
       to alts as a possible solution when a_i is the same local constant.

       If rhs is not a local constant, then for each a_i that is NOT a local constant, we add the constraints
                ?m  =?= fun x_1 ... x_k, x_i
                a_i =?= rhs
       to alts as a possible solution when a_i is the same local constant.
    */
    void add_simple_projections(expr const & m, buffer<expr> const & margs, expr const & rhs, justification const & j,
                                buffer<constraints> & alts) {
        lean_assert(is_metavar(m));
        lean_assert(!is_meta(rhs));
        lean_assert(!is_app(rhs));
        expr const & mtype = mlocal_type(m);
        unsigned vidx = margs.size() - 1;
        for (expr const & marg : margs) {
            if (!is_local(marg) && !is_local(rhs)) {
                // if rhs is not local, then we only add projections for the nonlocal arguments of lhs
                constraint c1 = mk_eq_cnstr(marg, rhs, j);
                constraint c2 = mk_eq_cnstr(m, mk_lambda_for(mtype, mk_var(vidx)), j);
                alts.push_back(constraints({c1, c2}));
            } else if (is_local(marg) && is_local(rhs) && mlocal_name(marg) == mlocal_name(rhs)) {
                // if the argument is local, and rhs is equal to it, then we also add a projection
                constraint c1 = mk_eq_cnstr(m, mk_lambda_for(mtype, mk_var(vidx)), j);
                alts.push_back(constraints(c1));
            }
            vidx--;
        }
    }

    /** \brief Process a flex rigid constraint */
    bool process_flex_rigid(expr const & lhs, expr const & rhs, justification const & j) {
        lean_assert(is_meta(lhs));
        lean_assert(!is_meta(rhs));
        buffer<expr> margs;
        expr m     = get_app_args(lhs, margs);
        for (expr & marg : margs)
            marg = m_tc.whnf(marg);
        buffer<constraints> alts;
        switch (rhs.kind()) {
        case expr_kind::Var: case expr_kind::Meta:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::Local:
            add_simple_projections(m, margs, rhs, j, alts);
            break;
        case expr_kind::Sort: case expr_kind::Constant:
            add_simple_projections(m, margs, rhs, j, alts);
            alts.push_back(mk_simple_imitation(m, rhs, j));
            break;
        case expr_kind::Pi: case expr_kind::Lambda:
            add_simple_projections(m, margs, rhs, j, alts);
            alts.push_back(mk_bindings_imitation(m, margs, rhs, j));
            break;
        case expr_kind::Macro:
            add_simple_projections(m, margs, rhs, j, alts);
            alts.push_back(mk_macro_imitation(m, margs, rhs, j));
            break;
        case expr_kind::App: {
            expr const & f = get_app_fn(rhs);
            lean_assert(is_constant(f) || is_local(f));
            if (is_local(f)) {
                unsigned vidx = margs.size() - 1;
                for (expr const & marg : margs) {
                    if (is_local(marg) && mlocal_name(marg) == mlocal_name(f))
                        alts.push_back(mk_flex_rigid_app_cnstrs(m, margs, mk_var(vidx), rhs, j));
                    vidx--;
                }
            } else if (is_constant(f)) {
                alts.push_back(mk_flex_rigid_app_cnstrs(m, margs, f, rhs, j));
            } else {
                lean_unreachable(); // LCOV_EXCL_LINE
            }
            break;
        }}

        if (alts.empty()) {
            set_conflict(j);
            return false;
        } else if (alts.size() == 1) {
            // we don't need to create a backtracking point
            return process_constraints(alts[0], justification());
        } else {
            justification a = mk_assumption_justification(m_next_assumption_idx);
            add_case_split(std::unique_ptr<case_split>(new ho_case_split(*this, to_list(alts.begin() + 1, alts.end()))));
            return process_constraints(alts[0], a);
        }
    }

    /** \brief Process a flex rigid constraint */
    bool process_flex_rigid(constraint const & c) {
        lean_assert(is_flex_rigid(c));
        if (is_meta(cnstr_lhs_expr(c)))
            return process_flex_rigid(cnstr_lhs_expr(c), cnstr_rhs_expr(c), c.get_justification());
        else
            return process_flex_rigid(cnstr_rhs_expr(c), cnstr_lhs_expr(c), c.get_justification());
    }

    bool process_flex_flex(constraint const &) {
        // We just ignore flex-flex constraints.
        // This kind of constraint does not occur very often.
        return true;
    }

    void consume_tc_cnstrs() {
        while (auto c = m_tc.next_cnstr()) {
            if (in_conflict())
                return;
            process_constraint(*c);
        }
    }

    /** \brief Process the next constraint in the constraint queue m_cnstrs */
    bool process_next() {
        lean_assert(!m_cnstrs.empty());
        constraint c = m_cnstrs.min()->first;
        m_cnstrs.erase_min();
        if (is_choice_cnstr(c))
            return process_choice_constraint(c);
        else if (is_flex_rigid(c))
            return process_flex_rigid(c);
        else if (is_flex_flex(c))
            return process_flex_flex(c);
        else
            return process_plugin_constraint(c);
    }

    /** \brief Produce the next solution */
    optional<substitution> next() {
        if (in_conflict())
            return failure();
        if (!m_case_splits.empty()) {
            justification all_assumptions;
            for (auto const & cs : m_case_splits)
                all_assumptions = mk_composite1(all_assumptions, mk_assumption_justification(cs->m_assumption_idx));
            set_conflict(all_assumptions);
            if (!resolve_conflict())
                return failure();
        } else if (m_first) {
            m_first = false;
        } else {
            // This is not the first run, and there are no case-splits.
            // We don't throw an exception since there are no more solutions.
            return optional<substitution>();
        }
        while (true) {
            consume_tc_cnstrs();
            if (!in_conflict()) {
                if (m_cnstrs.empty())
                    break;
                process_next();
            }
            if (in_conflict() && !resolve_conflict())
                return failure();
        }
        lean_assert(!in_conflict());
        lean_assert(m_cnstrs.empty());
        return optional<substitution>(m_subst);
    }
};

lazy_list<substitution> unify(std::shared_ptr<unifier_fn> u) {
    return mk_lazy_list<substitution>([=]() {
            auto s = u->next();
            if (s)
                return some(mk_pair(*s, unify(u)));
            else
                return lazy_list<substitution>::maybe_pair();
        });
}

lazy_list<substitution> unify(environment const & env,  unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              unifier_plugin const & p, bool use_exception, unsigned max_steps) {
    return unify(std::make_shared<unifier_fn>(env, num_cs, cs, ngen, substitution(), p, use_exception, max_steps));
}

lazy_list<substitution> unify(environment const & env,  unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              unifier_plugin const & p, options const & o) {
    return unify(env, num_cs, cs, ngen, p, get_unifier_use_exceptions(o), get_unifier_max_steps(o));
}

lazy_list<substitution> unify(environment const & env, unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              bool use_exception, unsigned max_steps) {
    return unify(env, num_cs, cs, ngen, [](constraint const &, name_generator const &) { return lazy_list<constraints>(); },
                 use_exception, max_steps);
}

lazy_list<substitution> unify(environment const & env, unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              options const & o) {
    return unify(env, num_cs, cs, ngen, get_unifier_use_exceptions(o), get_unifier_max_steps(o));
}

lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen, unifier_plugin const & p,
                              unsigned max_steps) {
    substitution s;
    name_generator new_ngen(ngen);
    type_checker tc(env, new_ngen.mk_child());
    if (!tc.is_def_eq(lhs, rhs))
        return lazy_list<substitution>();
    buffer<constraint> cs;
    while (auto c = tc.next_cnstr()) {
        cs.push_back(*c);
    }
    if (cs.empty()) {
        return lazy_list<substitution>(s);
    } else {
        return unify(std::make_shared<unifier_fn>(env, cs.size(), cs.data(), ngen, s, p, false, max_steps));
    }
}

lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen, unifier_plugin const & p,
                              options const & o) {
    return unify(env, lhs, rhs, ngen, p, get_unifier_max_steps(o));
}

lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen, unsigned max_steps) {
    return unify(env, lhs, rhs, ngen, [](constraint const &, name_generator const &) { return lazy_list<constraints>(); }, max_steps);
}

lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen, options const & o) {
    return unify(env, lhs, rhs, ngen, get_unifier_max_steps(o));
}

static int unify_simple(lua_State * L) {
    int nargs = lua_gettop(L);
    std::pair<unify_status, substitution> r;
    if (nargs == 2)
        r = unify_simple(to_substitution(L, 1), to_constraint(L, 2));
    else if (nargs == 3 && is_expr(L, 2))
        r = unify_simple(to_substitution(L, 1), to_expr(L, 2), to_expr(L, 3), justification());
    else if (nargs == 3 && is_level(L, 2))
        r = unify_simple(to_substitution(L, 1), to_level(L, 2), to_level(L, 3), justification());
    else if (is_expr(L, 2))
        r = unify_simple(to_substitution(L, 1), to_expr(L, 2), to_expr(L, 3), to_justification(L, 4));
    else
        r = unify_simple(to_substitution(L, 1), to_level(L, 2), to_level(L, 3), to_justification(L, 4));
    push_integer(L, static_cast<unsigned>(r.first));
    push_substitution(L, r.second);
    return 2;
}

typedef lazy_list<substitution> substitution_seq;
DECL_UDATA(substitution_seq)

static const struct luaL_Reg substitution_seq_m[] = {
    {"__gc", substitution_seq_gc},
    {0, 0}
};

static int substitution_seq_next(lua_State * L) {
    substitution_seq seq = to_substitution_seq(L, lua_upvalueindex(1));
    substitution_seq::maybe_pair p;
    p = seq.pull();
    if (p) {
        push_substitution_seq(L, p->second);
        lua_replace(L, lua_upvalueindex(1));
        push_substitution(L, p->first);
    } else {
        lua_pushnil(L);
    }
    return 1;
}

static int push_substitution_seq_it(lua_State * L, substitution_seq const & seq) {
    push_substitution_seq(L, seq);
    lua_pushcclosure(L, &safe_function<substitution_seq_next>, 1); // create closure with 1 upvalue
    return 1;
}

static void to_constraint_buffer(lua_State * L, int idx, buffer<constraint> & cs) {
    luaL_checktype(L, idx, LUA_TTABLE);
    lua_pushvalue(L, idx); // put table on top of the stack
    int n = objlen(L, idx);
    for (int i = 1; i <= n; i++) {
        lua_rawgeti(L, -1, i);
        cs.push_back(to_constraint(L, -1));
        lua_pop(L, 1);
    }
    lua_pop(L, 1);
}

static constraints to_constraints(lua_State * L, int idx) {
    buffer<constraint> cs;
    to_constraint_buffer(L, idx, cs);
    return to_list(cs.begin(), cs.end());
}

static unifier_plugin to_unifier_plugin(lua_State * L, int idx) {
    luaL_checktype(L, idx, LUA_TFUNCTION); // user-fun
    luaref f(L, idx);
    return unifier_plugin([=](constraint const & c, name_generator const & ngen) {
            lua_State * L = f.get_state();
            f.push();
            push_constraint(L, c);
            push_name_generator(L, ngen);
            pcall(L, 2, 1, 0);
            lazy_list<constraints> r;
            if (is_constraint(L, -1)) {
                // single constraint
                r = lazy_list<constraints>(constraints(to_constraint(L, -1)));
            } else if (lua_istable(L, -1)) {
                int num = objlen(L, -1);
                if (num == 0) {
                    // empty table
                    r = lazy_list<constraints>();
                } else {
                    lua_rawgeti(L, -1, 1);
                    if (is_constraint(L, -1)) {
                        // array of constraints case
                        lua_pop(L, 1);
                        r = lazy_list<constraints>(to_constraints(L, -1));
                    } else {
                        lua_pop(L, 1);
                        buffer<constraints> css;
                        // array of array of constraints
                        for (int i = 1; i <= num; i++) {
                            lua_rawgeti(L, -1, i);
                            css.push_back(to_constraints(L, -1));
                            lua_pop(L, 1);
                        }
                        r = to_lazy(to_list(css.begin(), css.end()));
                    }
                }
            } else if (lua_isnil(L, -1)) {
                // nil case
                r = lazy_list<constraints>();
            } else {
                throw exception("invalid unifier plugin, the result value must be a constrant, "
                                "nil, an array of constraints, or an array of arrays of constraints");
            }
            lua_pop(L, 1);
            return r;
        });
}

static name g_tmp_prefix = name::mk_internal_unique_name();

static int unify(lua_State * L) {
    int nargs = lua_gettop(L);
    lazy_list<substitution> r;
    environment const & env = to_environment(L, 1);
    if (is_expr(L, 2)) {
        if (nargs == 3)
            r = unify(env, to_expr(L, 2), to_expr(L, 3), name_generator(g_tmp_prefix));
        else if (nargs == 4 && is_options(L, 4))
            r = unify(env, to_expr(L, 2), to_expr(L, 3), name_generator(g_tmp_prefix), to_options(L, 4));
        else if (nargs == 4 && is_name_generator(L, 4))
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4));
        else if (nargs == 4)
            r = unify(env, to_expr(L, 2), to_expr(L, 3), name_generator(g_tmp_prefix), to_unifier_plugin(L, 4));
        else if (nargs == 5 && is_name_generator(L, 4) && is_options(L, 5))
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4), to_options(L, 5));
        else if (nargs == 5 && is_options(L, 5))
            r = unify(env, to_expr(L, 2), to_expr(L, 3), name_generator(g_tmp_prefix), to_unifier_plugin(L, 4), to_options(L, 5));
        else if (nargs == 5)
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4), to_unifier_plugin(L, 5));
        else
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4), to_unifier_plugin(L, 5), to_options(L, 6));
    } else {
        buffer<constraint> cs;
        to_constraint_buffer(L, 2, cs);
        if (nargs == 2)
            r = unify(env, cs.size(), cs.data(), name_generator(g_tmp_prefix));
        else if (nargs == 3 && is_name_generator(L, 3))
            r = unify(env, cs.size(), cs.data(), to_name_generator(L, 3));
        else if (nargs == 3 && is_options(L, 3))
            r = unify(env, cs.size(), cs.data(), name_generator(g_tmp_prefix), to_options(L, 3));
        else if (nargs == 3)
            r = unify(env, cs.size(), cs.data(), name_generator(g_tmp_prefix), to_unifier_plugin(L, 3));
        else if (nargs == 4 && is_name_generator(L, 3) && is_options(L, 4))
            r = unify(env, cs.size(), cs.data(), to_name_generator(L, 3), to_options(L, 4));
        else if (nargs == 4 && is_options(L, 4))
            r = unify(env, cs.size(), cs.data(), name_generator(g_tmp_prefix), to_unifier_plugin(L, 3), to_options(L, 4));
        else if (nargs == 4)
            r = unify(env, cs.size(), cs.data(), to_name_generator(L, 3), to_unifier_plugin(L, 4));
        else
            r = unify(env, cs.size(), cs.data(), to_name_generator(L, 3), to_unifier_plugin(L, 4), to_options(L, 5));
    }
    return push_substitution_seq_it(L, r);
}

void open_unifier(lua_State * L) {
    luaL_newmetatable(L, substitution_seq_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, substitution_seq_m, 0);
    SET_GLOBAL_FUN(substitution_seq_pred, "is_substitution_seq");

    SET_GLOBAL_FUN(unify_simple,  "unify_simple");
    SET_GLOBAL_FUN(unify,         "unify");

    lua_newtable(L);
    SET_ENUM("Solved",       unify_status::Solved);
    SET_ENUM("Failed",       unify_status::Failed);
    SET_ENUM("Unsupported",  unify_status::Unsupported);
    lua_setglobal(L, "unify_status");
}
}
