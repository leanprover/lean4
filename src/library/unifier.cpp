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
#include "library/opaque_hints.h"
#include "library/unifier_plugin.h"
#include "library/kernel_bindings.h"

namespace lean {
static name g_unifier_max_steps      {"unifier", "max_steps"};
RegisterUnsignedOption(g_unifier_max_steps, LEAN_DEFAULT_UNIFIER_MAX_STEPS, "(unifier) maximum number of steps");
unsigned get_unifier_max_steps(options const & opts) { return opts.get_unsigned(g_unifier_max_steps, LEAN_DEFAULT_UNIFIER_MAX_STEPS); }

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
            return has_local(e);
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
lbool occurs_context_check(substitution const & s, expr const & e, expr const & m, buffer<expr> const & locals) {
    expr root = e;
    lbool r = l_true;
    for_each(e, [&](expr const & e, unsigned) {
            if (r == l_false) {
                return false;
            } else if (is_local(e)) {
                if (std::find(locals.begin(), locals.end(), e) == locals.end()) {
                    // right-hand-side contains variable that is not in the scope
                    // of metavariable.
                    r = l_false;
                }
                return false; // do not visit type
            } else if (is_meta(e)) {
                if (!context_check(e, locals) || s.occurs(m, e))
                    r = l_undef;
                if (get_app_fn(e) == m)
                    r = l_false;
                return false; // do not visit children
            } else {
                // we only need to continue exploring e if it contains
                // metavariables and/or local constants.
                return has_expr_metavar(e) || has_local(e);
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
        switch (occurs_context_check(s, rhs, *m, args)) {
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
static unsigned g_group_size = 1u << 29;
static unsigned g_cnstr_group_first_index[6] = { 0, g_group_size, 2*g_group_size, 3*g_group_size, 4*g_group_size, 5*g_group_size};
static unsigned get_group_first_index(cnstr_group g) {
    return g_cnstr_group_first_index[static_cast<unsigned>(g)];
}

/** \brief Convert choice constraint delay factor to cnstr_group */
cnstr_group get_choice_cnstr_group(constraint const & c) {
    lean_assert(is_choice_cnstr(c));
    unsigned f = cnstr_delay_factor(c);
    if (f > static_cast<unsigned>(cnstr_group::MaxDelayed)) {
        return cnstr_group::MaxDelayed;
    } else {
        return static_cast<cnstr_group>(f);
    }
}

/** \brief Auxiliary functional object for implementing simultaneous higher-order unification */
struct unifier_fn {
    typedef std::pair<constraint, unsigned> cnstr; // constraint + idx
    struct cnstr_cmp {
        int operator()(cnstr const & c1, cnstr const & c2) const { return c1.second < c2.second ? -1 : (c1.second == c2.second ? 0 : 1); }
    };
    typedef rb_tree<cnstr, cnstr_cmp> cnstr_set;
    typedef rb_tree<unsigned, unsigned_cmp> cnstr_idx_set;
    typedef rb_map<name, cnstr_idx_set, name_quick_cmp> name_to_cnstrs;
    typedef std::unique_ptr<type_checker> type_checker_ptr;
    environment      m_env;
    name_generator   m_ngen;
    substitution     m_subst;
    unifier_plugin   m_plugin;
    type_checker_ptr m_tc;
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
        \brief The following map is an index. The map a metavariable name \c m to the set of constraint indices that contain \c m.
        We use these indices whenever a metavariable \c m is assigned.
        When the metavariable is assigned, we used this index to remove constraints that contains \c m from \c m_cnstrs,
        instantiate \c m, and reprocess them.

        \remark \c m_mvar_occs is for regular metavariables.
    */
    name_to_cnstrs   m_mvar_occs;

    /**
        \brief Base class for the case-splits created by the unifier.

        We have three different kinds of case splits:
        1- unifier plugin
        2- choice constraints
        3- higher-order unification
    */
    struct case_split {
        unsigned         m_assumption_idx; // idx of the current assumption
        justification    m_jst;
        justification    m_failed_justifications; // justifications for failed branches
        // snapshot of unifier's state
        substitution     m_subst;
        cnstr_set        m_cnstrs;
        name_to_cnstrs   m_mvar_occs;

        /** \brief Save unifier's state */
        case_split(unifier_fn & u, justification const & j):
            m_assumption_idx(u.m_next_assumption_idx), m_jst(j), m_subst(u.m_subst), m_cnstrs(u.m_cnstrs),
            m_mvar_occs(u.m_mvar_occs) {
            u.m_next_assumption_idx++;
            u.m_tc->push();
        }

        /** \brief Restore unifier's state with saved values, and update m_assumption_idx and m_failed_justifications. */
        void restore_state(unifier_fn & u) {
            lean_assert(u.in_conflict());
            u.m_tc->pop();   // restore type checker state
            u.m_tc->push();
            u.m_subst     = m_subst;
            u.m_cnstrs    = m_cnstrs;
            u.m_mvar_occs = m_mvar_occs;
            m_assumption_idx = u.m_next_assumption_idx;
            m_failed_justifications = mk_composite1(m_failed_justifications, *u.m_conflict);
            u.m_next_assumption_idx++;
            u.m_conflict  = optional<justification>();
        }
        justification get_jst() const { return m_jst; }
        virtual ~case_split() {}
        virtual bool next(unifier_fn & u) = 0;
    };
    typedef std::vector<std::unique_ptr<case_split>> case_split_stack;

    struct lazy_constraints_case_split : public case_split {
        lazy_list<constraints> m_tail;
        lazy_constraints_case_split(unifier_fn & u, justification const & j, lazy_list<constraints> const & tail):case_split(u, j), m_tail(tail) {}
        virtual bool next(unifier_fn & u) { return u.next_lazy_constraints_case_split(*this); }
    };

    struct simple_case_split : public case_split {
        list<constraints> m_tail;
        simple_case_split(unifier_fn & u, justification const & j, list<constraints> const & tail):case_split(u, j), m_tail(tail) {}
        virtual bool next(unifier_fn & u) { return u.next_simple_case_split(*this); }
    };

    case_split_stack        m_case_splits;
    optional<justification> m_conflict; //!< if different from none, then there is a conflict.

    unifier_fn(environment const & env, unsigned num_cs, constraint const * cs,
               name_generator const & ngen, substitution const & s,
               bool use_exception, unsigned max_steps):
        m_env(env), m_ngen(ngen), m_subst(s), m_plugin(get_unifier_plugin(env)),
        m_tc(mk_type_checker_with_hints(env, m_ngen.mk_child())),
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

    expr mk_local_for(expr const & b) {
        return mk_local(m_ngen.next(), binding_name(b), binding_domain(b), binding_info(b));
    }

    /**
        \brief Update occurrence index with entry <tt>m -> cidx</tt>, where \c m is the name of a metavariable,
        and \c cidx is the index of a constraint that contains \c m.
    */
    void add_mvar_occ(name const & m, unsigned cidx) {
        cnstr_idx_set s;
        auto it = m_mvar_occs.find(m);
        if (it)
            s = *it;
        if (!s.contains(cidx)) {
            s.insert(cidx);
            m_mvar_occs.insert(m, s);
        }
    }

    void add_meta_occ(expr const & m, unsigned cidx) {
        lean_assert(is_meta(m));
        add_mvar_occ(mlocal_name(get_app_fn(m)), cidx);
    }

    void add_meta_occs(expr const & e, unsigned cidx) {
        if (has_expr_metavar(e)) {
            for_each(e, [&](expr const & e, unsigned) {
                    if (is_meta(e)) {
                        add_meta_occ(e, cidx);
                        return false;
                    }
                    if (is_local(e))
                        return false;
                    return has_expr_metavar(e);
                });
        }
    }

    /** \brief Add constraint to the constraint queue */
    unsigned add_cnstr(constraint const & c, cnstr_group g) {
        unsigned cidx = m_next_cidx + get_group_first_index(g);
        m_cnstrs.insert(cnstr(c, cidx));
        m_next_cidx++;
        return cidx;
    }

    bool is_def_eq(expr const & t1, expr const & t2, justification const & j) {
        if (m_tc->is_def_eq(t1, t2, j)) {
            return true;
        } else {
            set_conflict(j);
            return false;
        }
    }

    /**
       \brief Assign \c v to metavariable \c m with justification \c j.
       The type of v and m are inferred, and is_def_eq is invoked.
       Any constraint that contains \c m is revisited.
    */
    bool assign(expr const & m, expr const & v, justification const & j) {
        lean_assert(is_metavar(m));
        m_subst.d_assign(m, v, j);
        expr m_type = mlocal_type(m);
        expr v_type = m_tc->infer(v);
        if (in_conflict())
            return false;
        if (!is_def_eq(m_type, v_type, j))
            return false;
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
        m_subst.d_assign(m, v, j);
        return true;
    }

    enum status { Solved, Failed, Continue };
    /**
       \brief Process constraints of the form <tt>lhs =?= rhs</tt> where lhs is of the form <tt>?m</tt> or <tt>(?m l_1 .... l_n)</tt>,
       where all \c l_i are distinct local variables. In this case, the method returns Solved, if the method assign succeeds.
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
        switch (occurs_context_check(m_subst, rhs, *m, locals)) {
        case l_false:
            set_conflict(j);
            return Failed;
        case l_undef:
            return Continue;
        case l_true:
            lean_assert(!m_subst.is_assigned(*m));
            if (assign(*m, lambda_abstract_locals(rhs, locals), j)) {
                return Solved;
            } else {
                return Failed;
            }
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    optional<declaration> is_delta(expr const & e) { return ::lean::is_delta(m_env, e); }

    /** \brief Return true if lhs and rhs are of the form (f ...) where f can be expanded */
    bool is_eq_deltas(expr const & lhs, expr const & rhs) {
        auto lhs_d = is_delta(lhs);
        auto rhs_d = is_delta(rhs);
        return lhs_d && rhs_d && is_eqp(*lhs_d, *rhs_d);
    }

    /** \brief Return true if the constraint is of the form (f ...) =?= (f ...), where f can be expanded. */
    bool is_delta_cnstr(constraint const & c) {
        return is_eq_cnstr(c) && is_eq_deltas(cnstr_lhs_expr(c), cnstr_rhs_expr(c));
    }

    std::pair<constraint, bool> instantiate_metavars(constraint const & c) {
        if (is_eq_cnstr(c)) {
            auto lhs_jst = m_subst.d_instantiate_metavars(cnstr_lhs_expr(c));
            auto rhs_jst = m_subst.d_instantiate_metavars(cnstr_rhs_expr(c));
            expr lhs = lhs_jst.first;
            expr rhs = rhs_jst.first;
            if (lhs != cnstr_lhs_expr(c) || rhs != cnstr_rhs_expr(c)) {
                return mk_pair(mk_eq_cnstr(lhs, rhs,
                                           mk_composite1(mk_composite1(c.get_justification(), lhs_jst.second), rhs_jst.second)),
                               true);
            }
        } else if (is_level_eq_cnstr(c)) {
            auto lhs_jst = m_subst.d_instantiate_metavars(cnstr_lhs_level(c));
            auto rhs_jst = m_subst.d_instantiate_metavars(cnstr_rhs_level(c));
            level lhs = lhs_jst.first;
            level rhs = rhs_jst.first;
            if (lhs != cnstr_lhs_level(c) || rhs != cnstr_rhs_level(c)) {
                return mk_pair(mk_level_eq_cnstr(lhs, rhs,
                                                 mk_composite1(mk_composite1(c.get_justification(), lhs_jst.second), rhs_jst.second)),
                               true);
            }
        }
        return mk_pair(c, false);
    }

    status process_eq_constraint_core(constraint const & c) {
        expr const & lhs = cnstr_lhs_expr(c);
        expr const & rhs = cnstr_rhs_expr(c);
        justification const & jst = c.get_justification();

        if (lhs == rhs)
            return Solved; // trivial constraint

        // Update justification using the justification of the instantiated metavariables
        if (!has_metavar(lhs) && !has_metavar(rhs)) {
            return is_def_eq(lhs, rhs, jst) ? Solved : Failed;
        }

        // Handle higher-order pattern matching.
        status st = process_metavar_eq(lhs, rhs, jst);
        if (st != Continue) return st;
        st = process_metavar_eq(rhs, lhs, jst);
        if (st != Continue) return st;

        return Continue;
    }

    expr instantiate_meta(expr const & e, justification & j) {
        expr const & f = get_app_fn(e);
        if (!is_metavar(f))
            return e;
        auto r = m_subst.d_instantiate_metavars(f);
        if (is_metavar(r.first))
            return e;
        buffer<expr> args;
        get_app_rev_args(e, args);
        j = mk_composite1(j, r.second);
        return apply_beta(r.first, args.size(), args.data());
    }

    expr instantiate_meta_args(expr const & e, justification & j) {
        if (!is_app(e))
            return e;
        buffer<expr> args;
        bool modified = false;
        expr const & f = get_app_rev_args(e, args);
        unsigned i = args.size();
        while (i > 0) {
            --i;
            expr new_arg = instantiate_meta(args[i], j);
            if (new_arg != args[i]) {
                modified = true;
                args[i]  = new_arg;
            }
        }
        if (!modified)
            return e;
        return mk_rev_app(f, args.size(), args.data());
    }

    status instantiate_eq_cnstr(constraint const & c) {
        justification j = c.get_justification();
        expr lhs = instantiate_meta(cnstr_lhs_expr(c), j);
        expr rhs = instantiate_meta(cnstr_rhs_expr(c), j);
        if (lhs != cnstr_lhs_expr(c) || rhs != cnstr_rhs_expr(c))
            return is_def_eq(lhs, rhs, j) ? Solved : Failed;
        lhs = instantiate_meta_args(lhs, j);
        rhs = instantiate_meta_args(rhs, j);
        if (lhs != cnstr_lhs_expr(c) || rhs != cnstr_rhs_expr(c))
            return is_def_eq(lhs, rhs, j) ? Solved : Failed;
        return Continue;
    }

    /** \brief Process an equality constraints. */
    bool process_eq_constraint(constraint const & c) {
        lean_assert(is_eq_cnstr(c));
        // instantiate assigned metavariables
        status st = instantiate_eq_cnstr(c);
        if (st != Continue) return st == Solved;
        st = process_eq_constraint_core(c);
        if (st != Continue) return st == Solved;

        expr const & lhs = cnstr_lhs_expr(c);
        expr const & rhs = cnstr_rhs_expr(c);

        if (is_eq_deltas(lhs, rhs)) {
            // we need to create a backtracking point for this one
            add_cnstr(c, cnstr_group::Basic);
        } else if (m_plugin->delay_constraint(*m_tc, c)) {
            unsigned cidx = add_cnstr(c, cnstr_group::PluginDelayed);
            add_meta_occs(lhs, cidx);
            add_meta_occs(rhs, cidx);
        } else if (is_meta(lhs) && is_meta(rhs)) {
            // flex-flex constraints are delayed the most.
            unsigned cidx = add_cnstr(c, cnstr_group::FlexFlex);
            add_meta_occ(lhs, cidx);
            add_meta_occ(rhs, cidx);
        } else if (is_meta(lhs)) {
            // flex-rigid constraints are delayed.
            unsigned cidx = add_cnstr(c, cnstr_group::FlexRigid);
            add_meta_occ(lhs, cidx);
        } else if (is_meta(rhs)) {
            // flex-rigid constraints are delayed.
            unsigned cidx = add_cnstr(c, cnstr_group::FlexRigid);
            add_meta_occ(rhs, cidx);
        } else {
            // this constraints require the unifier plugin to be solved
            add_cnstr(c, cnstr_group::Basic);
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
            return Solved;
        } else {
            return Failed;
        }
    }

    /** \brief Process a universe level contraints. */
    bool process_level_eq_constraint(constraint const & c) {
        lean_assert(is_level_eq_cnstr(c));
        // instantiate assigned metavariables
        constraint new_c = instantiate_metavars(c).first;
        level lhs = cnstr_lhs_level(new_c);
        level rhs = cnstr_rhs_level(new_c);
        justification jst = new_c.get_justification();

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

        if (!has_meta(lhs) && !has_meta(rhs)) {
            set_conflict(jst);
            return false; // trivial failure
        }

        status st = process_metavar_eq(lhs, rhs, jst);
        if (st != Continue) return st == Solved;
        st = process_metavar_eq(rhs, lhs, jst);
        if (st != Continue) return st == Solved;

        add_cnstr(new_c, cnstr_group::FlexRigid);
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
            add_cnstr(c, get_choice_cnstr_group(c));
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
        out << j.pp(mk_simple_formatter_factory()(m_env, options()), nullptr, m_subst) << "\n";
        if (j.is_composite()) {
            display(out, composite_child1(j), indent+2);
            display(out, composite_child2(j), indent+2);
        }
    }

    void pop_case_split() {
        m_tc->pop();
        m_case_splits.pop_back();
    }

    bool resolve_conflict() {
        lean_assert(in_conflict());
        while (!m_case_splits.empty()) {
            justification conflict = *m_conflict;
            std::unique_ptr<case_split> & d = m_case_splits.back();
            if (depends_on(conflict, d->m_assumption_idx)) {
                d->m_failed_justifications = mk_composite1(d->m_failed_justifications, conflict);
                if (d->next(*this)) {
                    reset_conflict();
                    return true;
                }
            } else {
                pop_case_split();
            }
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

    bool next_lazy_constraints_case_split(lazy_constraints_case_split & cs) {
        auto r = cs.m_tail.pull();
        if (r) {
            cs.restore_state(*this);
            lean_assert(!in_conflict());
            cs.m_tail = r->second;
            return process_constraints(r->first, mk_composite1(cs.get_jst(), mk_assumption_justification(cs.m_assumption_idx)));
        } else {
            // update conflict
            update_conflict(mk_composite1(*m_conflict, cs.m_failed_justifications));
            pop_case_split();
            return false;
        }
    }

    bool process_lazy_constraints(lazy_list<constraints> const & l, justification const & j) {
        auto r = l.pull();
        if (r) {
            if (r->second.is_nil()) {
                // there is only one alternative
                return process_constraints(r->first, j);
            } else {
                justification a = mk_assumption_justification(m_next_assumption_idx);
                add_case_split(std::unique_ptr<case_split>(new lazy_constraints_case_split(*this, j, r->second)));
                return process_constraints(r->first, mk_composite1(j, a));
            }
        } else {
            set_conflict(j);
            return false;
        }
    }

    bool process_plugin_constraint(constraint const & c) {
        lean_assert(!is_choice_cnstr(c));
        lazy_list<constraints> alts = m_plugin->solve(*m_tc, c, m_ngen.mk_child());
        return process_lazy_constraints(alts, c.get_justification());
    }

    bool process_choice_constraint(constraint const & c) {
        lean_assert(is_choice_cnstr(c));
        expr const &   m            = cnstr_expr(c);
        choice_fn const & fn        = cnstr_choice_fn(c);
        auto m_type_jst             = m_subst.d_instantiate_metavars(m_tc->infer(m));
        lazy_list<constraints> alts = fn(m, m_type_jst.first, m_subst, m_ngen.mk_child());
        return process_lazy_constraints(alts, mk_composite1(c.get_justification(), m_type_jst.second));
    }

    bool next_simple_case_split(simple_case_split & cs) {
        if (!is_nil(cs.m_tail)) {
            cs.restore_state(*this);
            lean_assert(!in_conflict());
            constraints c = head(cs.m_tail);
            cs.m_tail     = tail(cs.m_tail);
            return process_constraints(c, mk_composite1(cs.get_jst(), mk_assumption_justification(cs.m_assumption_idx)));
        } else {
            // update conflict
            update_conflict(mk_composite1(*m_conflict, cs.m_failed_justifications));
            pop_case_split();
            return false;
        }
    }

    /**
        \brief Solve constraints of the form (f a_1 ... a_n) =?= (f b_1 ... b_n) where f can be expanded.
        We consider two possible solutions:
        1)   a_1 =?= b_1, ..., a_n =?= b_n
        2)   t =?= s, where t and s are the terms we get after expanding f
    */
    bool process_delta(constraint const & c) {
        lean_assert(is_delta_cnstr(c));
        expr const & lhs = cnstr_lhs_expr(c);
        expr const & rhs = cnstr_rhs_expr(c);
        buffer<expr> lhs_args, rhs_args;
        justification j = c.get_justification();
        expr lhs_fn     = get_app_rev_args(lhs, lhs_args);
        expr rhs_fn     = get_app_rev_args(rhs, rhs_args);
        declaration d   = *m_env.find(const_name(lhs_fn));
        levels lhs_lvls = const_levels(lhs_fn);
        levels rhs_lvls = const_levels(lhs_fn);
        if (lhs_args.size() != rhs_args.size() ||
            length(lhs_lvls) != length(rhs_lvls) ||
            length(d.get_univ_params()) != length(lhs_lvls)) {
            // the constraint is not well-formed, this can happen when users are abusing the API
            return false;
        }

        justification a = mk_assumption_justification(m_next_assumption_idx);

        // add case_split for t =?= s
        expr lhs_fn_val = instantiate_univ_params(d.get_value(), d.get_univ_params(), const_levels(lhs_fn));
        expr rhs_fn_val = instantiate_univ_params(d.get_value(), d.get_univ_params(), const_levels(rhs_fn));
        expr t = apply_beta(lhs_fn_val, lhs_args.size(), lhs_args.data());
        expr s = apply_beta(rhs_fn_val, rhs_args.size(), rhs_args.data());
        constraints cs2(mk_eq_cnstr(t, s, j));
        add_case_split(std::unique_ptr<case_split>(new simple_case_split(*this, j, list<constraints>(cs2))));

        // process first case
        justification new_j = mk_composite1(j, a);
        while (!is_nil(lhs_lvls)) {
            level lhs = head(lhs_lvls);
            level rhs = head(rhs_lvls);
            if (!process_constraint(mk_level_eq_cnstr(lhs, rhs, new_j)))
                return false;
            lhs_lvls = tail(lhs_lvls);
            rhs_lvls = tail(rhs_lvls);
        }

        unsigned i = lhs_args.size();
        while (i > 0) {
            --i;
            if (!is_def_eq(lhs_args[i], rhs_args[i], new_j))
                return false;
        }
        return true;
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
       \brief Given t
           <tt>Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), B[x_1, ..., x_n]</tt>
       return
           <tt>fun (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), v[x_1, ... x_n]</tt>

       \remark v has free variables.
    */
    expr mk_lambda_for(expr const & t, expr const & v) {
        if (is_pi(t)) {
            return mk_lambda(binding_name(t), binding_domain(t), mk_lambda_for(binding_body(t), v), binding_info(t));
        } else {
            return v;
        }
    }

    /** \see ensure_sufficient_args */
    optional<expr> ensure_sufficient_args_core(expr mtype, unsigned i, buffer<expr> const & margs) {
        if (i == margs.size())
            return some_expr(mtype);
        mtype = m_tc->ensure_pi(mtype);
        if (!m_tc->is_def_eq(binding_domain(mtype), m_tc->infer(margs[i])))
            return none_expr();
        expr local = mk_local_for(mtype);
        expr body  = instantiate(binding_body(mtype), local);
        auto new_body = ensure_sufficient_args_core(body, i+1, margs);
        if (!new_body)
            return none_expr();
        return some_expr(Pi(local, *new_body));
    }

    /**
       \brief Make sure mtype is a Pi of size at least margs.size().
       If it is not, we use ensure_pi and (potentially) add new constaints to enforce it.
    */
    optional<expr> ensure_sufficient_args(expr const & mtype, buffer<expr> const & margs, buffer<constraint> & cs, justification const & j) {
        expr t = mtype;
        unsigned num = 0;
        while (is_pi(t)) {
            num++;
            t = binding_body(t);
        }
        if (num == margs.size())
            return some_expr(mtype);;
        lean_assert(!m_tc->next_cnstr()); // make sure there are no pending constraints
        // We must create a scope to make sure no constraints "leak" into the current state.
        type_checker::scope scope(*m_tc);
        auto new_mtype = ensure_sufficient_args_core(mtype, 0, margs);
        if (!new_mtype)
            return none_expr();
        while (auto c = m_tc->next_cnstr())
            cs.push_back(update_justification(*c, mk_composite1(c->get_justification(), j)));
        return new_mtype;
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
    void mk_flex_rigid_app_cnstrs(expr const & m, buffer<expr> const & margs, expr const & f, expr const & rhs, justification const & j,
                                  buffer<constraints> & alts) {
        lean_assert(is_metavar(m));
        lean_assert(is_app(rhs));
        lean_assert(is_constant(f) || is_var(f));
        buffer<constraint> cs;
        expr mtype = mlocal_type(m);
        auto new_mtype = ensure_sufficient_args(mtype, margs, cs, j);
        if (!new_mtype) return;
        mtype = *new_mtype;
        buffer<expr> rargs;
        get_app_args(rhs, rargs);
        buffer<expr> sargs;
        for (expr const & rarg : rargs) {
            expr maux = mk_aux_metavar_for(m_ngen, mtype);
            cs.push_back(mk_eq_cnstr(mk_app(maux, margs), rarg, j));
            sargs.push_back(mk_app_vars(maux, margs.size()));
        }
        expr v = mk_app(f, sargs);
        v = mk_lambda_for(mtype, v);
        cs.push_back(mk_eq_cnstr(m, v, j));
        alts.push_back(to_list(cs.begin(), cs.end()));
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
    void mk_bindings_imitation(expr const & m, buffer<expr> const & margs, expr const & rhs, justification const & j,
                               buffer<constraints> & alts) {
        lean_assert(is_metavar(m));
        lean_assert(is_binding(rhs));
        buffer<constraint> cs;
        expr mtype = mlocal_type(m);
        auto new_mtype = ensure_sufficient_args(mtype, margs, cs, j);
        if (!new_mtype) return;
        mtype = *new_mtype;
        expr maux1  = mk_aux_metavar_for(m_ngen, mtype);
        cs.push_back(mk_eq_cnstr(mk_app(maux1, margs), binding_domain(rhs), j));
        expr dontcare;
        expr tmp_pi = mk_pi(binding_name(rhs), mk_app_vars(maux1, margs.size()), dontcare); // trick for "extending" the context
        expr mtype2 = replace_range(mtype, tmp_pi); // trick for "extending" the context
        expr maux2  = mk_aux_metavar_for(m_ngen, mtype2);
        expr new_local = mk_local_for(rhs);
        cs.push_back(mk_eq_cnstr(mk_app(mk_app(maux2, margs), new_local), instantiate(binding_body(rhs), new_local), j));
        expr v = update_binding(rhs, mk_app_vars(maux1, margs.size()), mk_app_vars(maux2, margs.size() + 1));
        v = mk_lambda_for(mtype, v);
        cs.push_back(mk_eq_cnstr(m, v, j));
        alts.push_back(to_list(cs.begin(), cs.end()));
    }

    /**
       \brief Given
                 m      := a metavariable ?m
                 rhs    := sort, constant
        Then solve (?m a_1 ... a_k) =?= rhs, by returning the constraint
                 ?m  =?= fun (x1 ... x_k), rhs
    */
    void mk_simple_imitation(expr const & m, expr const & rhs, justification const & j, buffer<constraints> & alts) {
        lean_assert(is_metavar(m));
        lean_assert(is_sort(rhs) || is_constant(rhs));
        expr const & mtype = mlocal_type(m);
        buffer<constraint> cs;
        cs.push_back(mk_eq_cnstr(m, mk_lambda_for(mtype, rhs), j));
        alts.push_back(to_list(cs.begin(), cs.end()));
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
    void mk_macro_imitation(expr const & m, buffer<expr> const & margs, expr const & rhs, justification const & j,
                            buffer<constraints> & alts) {
        lean_assert(is_metavar(m));
        lean_assert(is_macro(rhs));
        buffer<constraint> cs;
        expr mtype = mlocal_type(m);
        auto new_mtype = ensure_sufficient_args(mtype, margs, cs, j);
        if (!new_mtype) return;
        mtype = *new_mtype;
        // create an auxiliary metavariable for each macro argument
        buffer<expr> sargs;
        for (unsigned i = 0; i < macro_num_args(rhs); i++) {
            expr maux = mk_aux_metavar_for(m_ngen, mtype);
            cs.push_back(mk_eq_cnstr(mk_app(maux, margs), macro_arg(rhs, i), j));
            sargs.push_back(mk_app_vars(maux, margs.size()));
        }
        expr v = mk_macro(macro_def(rhs), sargs.size(), sargs.data());
        v = mk_lambda_for(mtype, v);
        cs.push_back(mk_eq_cnstr(m, v, j));
        alts.push_back(to_list(cs.begin(), cs.end()));
    }

    /**
       Given,
               m      := a metavariable ?m
               margs  := [a_1 ... a_k]
       We say a unification problem (?m a_1 ... a_k) =?= rhs uses "simple projections" when

       If (rhs and a_i are *not* local constants) OR (rhs is a local constant and a_i is a metavariable application),
       then we add the constraints
                a_i =?= rhs
                ?m  =?= fun x_1 ... x_k, x_i
       to alts as a possible solution.

       If rhs is a local constant and a_i == rhs, then we add the constraint
                ?m =?= fun x_1 ... x_k, x_i
       to alts as a possible solution when a_i is the same local constant or a metavariable application

    */
    void mk_simple_projections(expr const & m, buffer<expr> const & margs, expr const & rhs, justification const & j,
                                buffer<constraints> & alts) {
        lean_assert(is_metavar(m));
        lean_assert(!is_meta(rhs));
        expr const & mtype = mlocal_type(m);
        unsigned i = margs.size();
        while (i > 0) {
            unsigned vidx = margs.size() - i;
            --i;
            expr const & marg = margs[i];
            if ((!is_local(marg) && !is_local(rhs)) || (is_meta(marg) && is_local(rhs))) {
                // if rhs is not local, then we only add projections for the nonlocal arguments of lhs
                buffer<constraint> cs;
                if (auto new_mtype = ensure_sufficient_args(mtype, margs, cs, j)) {
                    cs.push_back(mk_eq_cnstr(marg, rhs, j));
                    expr v = mk_lambda_for(*new_mtype, mk_var(vidx));
                    cs.push_back(mk_eq_cnstr(m, v, j));
                    alts.push_back(to_list(cs.begin(), cs.end()));
                }
            } else if (is_local(marg) && is_local(rhs) && mlocal_name(marg) == mlocal_name(rhs)) {
                // if the argument is local, and rhs is equal to it, then we also add a projection
                buffer<constraint> cs;
                if (auto new_mtype = ensure_sufficient_args(mtype, margs, cs, j)) {
                    expr v = mk_lambda_for(*new_mtype, mk_var(vidx));
                    cs.push_back(mk_eq_cnstr(m, v, j));
                    alts.push_back(to_list(cs.begin(), cs.end()));
                }
            }
        }
    }

    /** \brief Process a flex rigid constraint */
    bool process_flex_rigid(expr const & lhs, expr const & rhs, justification const & j) {
        lean_assert(is_meta(lhs));
        lean_assert(!is_meta(rhs));
        buffer<expr> margs;
        expr m     = get_app_args(lhs, margs);
        for (expr & marg : margs)
            marg = m_tc->whnf(marg);
        buffer<constraints> alts;
        switch (rhs.kind()) {
        case expr_kind::Var: case expr_kind::Meta:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::Local:
            mk_simple_projections(m, margs, rhs, j, alts);
            break;
        case expr_kind::Sort: case expr_kind::Constant:
            mk_simple_projections(m, margs, rhs, j, alts);
            mk_simple_imitation(m, rhs, j, alts);
            break;
        case expr_kind::Pi: case expr_kind::Lambda:
            mk_simple_projections(m, margs, rhs, j, alts);
            mk_bindings_imitation(m, margs, rhs, j, alts);
            break;
        case expr_kind::Macro:
            mk_simple_projections(m, margs, rhs, j, alts);
            mk_macro_imitation(m, margs, rhs, j, alts);
            break;
        case expr_kind::App: {
            expr const & f = get_app_fn(rhs);
            if (is_local(f)) {
                unsigned i = margs.size();
                while (i > 0) {
                    unsigned vidx = margs.size() - i;
                    --i;
                    expr const & marg = margs[i];
                    if (is_local(marg) && mlocal_name(marg) == mlocal_name(f))
                        mk_flex_rigid_app_cnstrs(m, margs, mk_var(vidx), rhs, j, alts);
                }
            } else if (is_constant(f)) {
                mk_simple_projections(m, margs, rhs, j, alts);
                mk_flex_rigid_app_cnstrs(m, margs, f, rhs, j, alts);
            } else {
                expr new_rhs = m_tc->whnf(rhs);
                lean_assert(new_rhs != rhs);
                return is_def_eq(lhs, new_rhs, j);
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
            add_case_split(std::unique_ptr<case_split>(new simple_case_split(*this, j, to_list(alts.begin() + 1, alts.end()))));
            return process_constraints(alts[0], a);
        }
    }

    /** \brief Process a flex rigid constraint */
    bool process_flex_rigid(constraint const & c) {
        lean_assert(is_flex_rigid(c));
        expr lhs = cnstr_lhs_expr(c);
        expr rhs = cnstr_rhs_expr(c);
        if (is_meta(lhs))
            return process_flex_rigid(lhs, rhs, c.get_justification());
        else
            return process_flex_rigid(rhs, lhs, c.get_justification());
    }

    bool process_flex_flex(constraint const & c) {
        expr const & lhs = cnstr_lhs_expr(c);
        expr const & rhs = cnstr_rhs_expr(c);
        // We ignore almost all flex-flex constraints.
        // We just handle flex_flex "first-order" case
        //   ?M_1 l_1 ... l_k =?= ?M_2 l_1 ... l_k
        if (!is_simple_meta(lhs) || !is_simple_meta(rhs))
            return true;
        buffer<expr> lhs_args, rhs_args;
        expr ml = get_app_args(lhs, lhs_args);
        expr mr = get_app_args(rhs, rhs_args);
        if (ml == mr || lhs_args.size() != rhs_args.size())
            return true;
        lean_assert(!m_subst.is_assigned(ml));
        lean_assert(!m_subst.is_assigned(mr));
        unsigned i = 0;
        for (; i < lhs_args.size(); i++)
            if (lhs_args[i] != rhs_args[i])
                break;
        if (i == lhs_args.size())
            return assign(ml, mr, c.get_justification());
        return true;
    }

    void consume_tc_cnstrs() {
        while (true) {
            if (in_conflict())
                return;
            if (auto c = m_tc->next_cnstr()) {
                process_constraint(*c);
            } else {
                break;
            }
        }
    }

    /** \brief Process the next constraint in the constraint queue m_cnstrs */
    bool process_next() {
        lean_assert(!m_cnstrs.empty());
        constraint c = m_cnstrs.min()->first;
        m_cnstrs.erase_min();
        if (is_choice_cnstr(c)) {
            return process_choice_constraint(c);
        } else {
            auto r = instantiate_metavars(c);
            c = r.first;
            bool modified = r.second;
            if (is_level_eq_cnstr(c)) {
                if (modified)
                    return process_constraint(c);
                else
                    return process_plugin_constraint(c);
            } else {
                lean_assert(is_eq_cnstr(c));
                if (is_delta_cnstr(c))
                    return process_delta(c);
                else if (modified)
                    return is_def_eq(cnstr_lhs_expr(c), cnstr_rhs_expr(c), c.get_justification());
                else if (is_flex_rigid(c))
                    return process_flex_rigid(c);
                else if (is_flex_flex(c))
                    return process_flex_flex(c);
                else
                    return process_plugin_constraint(c);
            }
        }
    }

    /** \brief Return true if unifier may be able to produce more solutions */
    bool more_solutions() const {
        return !in_conflict() || !m_case_splits.empty();
    }

    /** \brief Produce the next solution */
    optional<substitution> next() {
        if (!more_solutions())
            return failure();
        if (!m_first && !m_case_splits.empty()) {
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
        return optional<substitution>(m_subst.forget_justifications());
    }
};

lazy_list<substitution> unify(std::shared_ptr<unifier_fn> u) {
    if (!u->more_solutions()) {
        u->failure(); // make sure exception is thrown if u->m_use_exception is true
        return lazy_list<substitution>();
    } else {
        return mk_lazy_list<substitution>([=]() {
                auto s = u->next();
                if (s)
                    return some(mk_pair(*s, unify(u)));
                else
                    return lazy_list<substitution>::maybe_pair();
            });
    }
}

lazy_list<substitution> unify(environment const & env,  unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              bool use_exception, unsigned max_steps) {
    return unify(std::make_shared<unifier_fn>(env, num_cs, cs, ngen, substitution(), use_exception, max_steps));
}

lazy_list<substitution> unify(environment const & env,  unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              bool use_exception, options const & o) {
    return unify(env, num_cs, cs, ngen, use_exception, get_unifier_max_steps(o));
}

lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen, substitution const & s,
                              unsigned max_steps) {
    auto u = std::make_shared<unifier_fn>(env, 0, nullptr, ngen, s, false, max_steps);
    expr _lhs = s.instantiate(lhs);
    expr _rhs = s.instantiate(rhs);
    if (!u->m_tc->is_def_eq(_lhs, _rhs))
        return lazy_list<substitution>();
    else
        return unify(u);
}

lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen,
                              substitution const & s, options const & o) {
    return unify(env, lhs, rhs, ngen, s, get_unifier_max_steps(o));
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

#if 0
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
#endif

static name g_tmp_prefix = name::mk_internal_unique_name();

static int unify(lua_State * L) {
    int nargs = lua_gettop(L);
    lazy_list<substitution> r;
    environment const & env = to_environment(L, 1);
    if (is_expr(L, 2)) {
        if (nargs == 6)
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4), to_substitution(L, 5), to_options(L, 6));
        else
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4), to_substitution(L, 5), options());
    } else {
        buffer<constraint> cs;
        to_constraint_buffer(L, 2, cs);
        if (nargs == 4)
            r = unify(env, cs.size(), cs.data(), to_name_generator(L, 3), false, to_options(L, 4));
        else
            r = unify(env, cs.size(), cs.data(), to_name_generator(L, 3), false, options());
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
