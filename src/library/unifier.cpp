/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <memory>
#include <vector>
#include <limits>
#include <algorithm>
#include "util/interrupt.h"
#include "util/luaref.h"
#include "util/lazy_list_fn.h"
#include "util/sstream.h"
#include "util/lbool.h"
#include "util/flet.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/for_each_fn.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "kernel/error_msgs.h"
#include "library/normalize.h"
#include "library/occurs.h"
#include "library/locals.h"
#include "library/module.h"
#include "library/unifier.h"
#include "library/reducible.h"
#include "library/unifier_plugin.h"
#include "library/kernel_bindings.h"
#include "library/print.h"
#include "library/expr_lt.h"
#include "library/projection.h"
#include "library/coercion.h"

#ifndef LEAN_DEFAULT_UNIFIER_MAX_STEPS
#define LEAN_DEFAULT_UNIFIER_MAX_STEPS 20000
#endif

#ifndef LEAN_DEFAULT_UNIFIER_COMPUTATION
#define LEAN_DEFAULT_UNIFIER_COMPUTATION false
#endif

#ifndef LEAN_DEFAULT_UNIFIER_EXPENSIVE_CLASSES
#define LEAN_DEFAULT_UNIFIER_EXPENSIVE_CLASSES false
#endif

#ifndef LEAN_DEFAULT_UNIFIER_CONSERVATIVE
#define LEAN_DEFAULT_UNIFIER_CONSERVATIVE false
#endif

#ifndef LEAN_DEFAULT_UNIFIER_NONCHRONOLOGICAL
#define LEAN_DEFAULT_UNIFIER_NONCHRONOLOGICAL true
#endif

#ifndef LEAN_DEFAULT_UNIFIER_NORMALIZER_MAX_STEPS
#define LEAN_DEFAULT_UNIFIER_NORMALIZER_MAX_STEPS 512
#endif

namespace lean {
static name * g_unifier_max_steps               = nullptr;
static name * g_unifier_computation             = nullptr;
static name * g_unifier_expensive_classes       = nullptr;
static name * g_unifier_conservative            = nullptr;
static name * g_unifier_nonchronological        = nullptr;
static name * g_unifier_normalizer_max_steps    = nullptr;

unsigned get_unifier_max_steps(options const & opts) {
    return opts.get_unsigned(*g_unifier_max_steps, LEAN_DEFAULT_UNIFIER_MAX_STEPS);
}

unsigned get_unifier_normalizer_max_steps(options const & opts) {
    return opts.get_unsigned(*g_unifier_normalizer_max_steps, LEAN_DEFAULT_UNIFIER_NORMALIZER_MAX_STEPS);
}

bool get_unifier_computation(options const & opts) {
    return opts.get_bool(*g_unifier_computation, LEAN_DEFAULT_UNIFIER_COMPUTATION);
}

bool get_unifier_expensive_classes(options const & opts) {
    return opts.get_bool(*g_unifier_expensive_classes, LEAN_DEFAULT_UNIFIER_EXPENSIVE_CLASSES);
}

bool get_unifier_conservative(options const & opts) {
    return opts.get_bool(*g_unifier_conservative, LEAN_DEFAULT_UNIFIER_CONSERVATIVE);
}

bool get_unifier_nonchronological(options const & opts) {
    return opts.get_bool(*g_unifier_nonchronological, LEAN_DEFAULT_UNIFIER_NONCHRONOLOGICAL);
}

unifier_config::unifier_config(bool use_exceptions, bool discard):
    m_use_exceptions(use_exceptions),
    m_max_steps(LEAN_DEFAULT_UNIFIER_MAX_STEPS),
    m_normalizer_max_steps(LEAN_DEFAULT_UNIFIER_NORMALIZER_MAX_STEPS),
    m_computation(LEAN_DEFAULT_UNIFIER_COMPUTATION),
    m_expensive_classes(LEAN_DEFAULT_UNIFIER_EXPENSIVE_CLASSES),
    m_discard(discard),
    m_nonchronological(LEAN_DEFAULT_UNIFIER_NONCHRONOLOGICAL) {
    m_kind    = unifier_kind::Liberal;
    m_pattern = false;
    m_ignore_context_check = false;
}

unifier_config::unifier_config(options const & o, bool use_exceptions, bool discard):
    m_use_exceptions(use_exceptions),
    m_max_steps(get_unifier_max_steps(o)),
    m_normalizer_max_steps(get_unifier_normalizer_max_steps(o)),
    m_computation(get_unifier_computation(o)),
    m_expensive_classes(get_unifier_expensive_classes(o)),
    m_discard(discard),
    m_nonchronological(get_unifier_nonchronological(o)) {
    if (get_unifier_conservative(o))
        m_kind = unifier_kind::Conservative;
    else
        m_kind = unifier_kind::Liberal;
    m_pattern = false;
    m_ignore_context_check = false;
}

// If \c e is a metavariable ?m or a term of the form (?m l_1 ... l_n) where
// l_1 ... l_n are distinct local variables, then return ?m, and store l_1 ... l_n in args.
// Otherwise return none.
optional<expr> is_simple_meta(expr const & e, buffer<expr> & args) {
    expr const & m = get_app_args(e, args);
    if (!is_metavar(m))
        return none_expr();
    for (auto it = args.begin(); it != args.end(); it++) {
        if (!is_local(*it) || contains_local(*it, args.begin(), it))
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
            if (is_local(e)) {
                if (!contains_local(e, locals))
                    failed = true;
                return false; // do not visit type
            }
            if (is_metavar(e))
                return false; // do not visit type
            return has_local(e);
        });
    return !failed;
}

enum class occurs_check_status { Ok, Maybe, FailCircular, FailLocal };

// Return
//   - l_undef if \c e contains a metavariable application that contains
//     a local constant not in locals
//   - l_true if \c e does not contain the metavariable \c m, and all local
//     constants are in \c e are in \c locals.
//   - l_false if \c e contains \c m or it contains a local constant \c l
//     not in locals that is not in a metavariable application.
occurs_check_status occurs_context_check(substitution & s, expr const & e, expr const & m, buffer<expr> const & locals, expr & bad_local) {
    expr root = e;
    occurs_check_status r = occurs_check_status::Ok;
    for_each(e, [&](expr const & e, unsigned) {
            if (r == occurs_check_status::FailLocal || r == occurs_check_status::FailCircular) {
                return false;
            } else if (is_local(e)) {
                if (!contains_local(e, locals)) {
                    // right-hand-side contains variable that is not in the scope
                    // of metavariable.
                    bad_local = e;
                    r = occurs_check_status::FailLocal;
                }
                return false; // do not visit type
            } else if (is_meta(e)) {
                if (r == occurs_check_status::Ok) {
                    if (!context_check(e, locals))
                        r = occurs_check_status::Maybe;
                    if (s.occurs(m, e))
                        r = occurs_check_status::Maybe;
                }
                if (mlocal_name(get_app_fn(e)) == mlocal_name(m))
                    r = occurs_check_status::FailCircular;
                return false; // do not visit children
            } else {
                // we only need to continue exploring e if it contains
                // metavariables and/or local constants.
                return has_expr_metavar(e) || has_local(e);
            }
        });
    if (r != occurs_check_status::Ok)
        return r;
    for (expr const & local : locals) {
        if (s.occurs(m, mlocal_type(local)))
            return occurs_check_status::Maybe;
    }
    return r;
}

occurs_check_status occurs_context_check(substitution & s, expr const & e, expr const & m, buffer<expr> const & locals) {
    expr bad_local;
    return occurs_context_check(s, e, m, locals, bad_local);
}

unify_status unify_simple_core(substitution & s, expr const & lhs, expr const & rhs, justification const & j) {
    lean_assert(is_meta(lhs));
    buffer<expr> args;
    auto m = is_simple_meta(lhs, args);
    if (!m || is_meta(rhs)) {
        return unify_status::Unsupported;
    } else {
        switch (occurs_context_check(s, rhs, *m, args)) {
        case occurs_check_status::FailLocal:
        case occurs_check_status::FailCircular:
            return unify_status::Failed;
        case occurs_check_status::Maybe:
            return unify_status::Unsupported;
        case occurs_check_status::Ok: {
            s.assign(*m, args, rhs, j);
            return unify_status::Solved;
        }}
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

unify_status unify_simple(substitution & s, expr const & lhs, expr const & rhs, justification const & j) {
    if (lhs == rhs)
        return unify_status::Solved;
    else if (!has_metavar(lhs) && !has_metavar(rhs))
        return unify_status::Failed;
    else if (is_meta(lhs))
        return unify_simple_core(s, lhs, rhs, j);
    else if (is_meta(rhs))
        return unify_simple_core(s, rhs, lhs, j);
    else
        return unify_status::Unsupported;
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

unify_status unify_simple_core(substitution & s, level const & lhs, level const & rhs, justification const & j) {
    lean_assert(is_meta(lhs));
    bool contains = occurs_meta(lhs, rhs);
    if (contains) {
        if (is_succ(rhs))
            return unify_status::Failed;
        else
            return unify_status::Unsupported;
    }
    s.assign(meta_id(lhs), rhs, j);
    return unify_status::Solved;
}

unify_status unify_simple(substitution & s, level const & lhs, level const & rhs, justification const & j) {
    if (lhs == rhs)
        return unify_status::Solved;
    else if (!has_meta(lhs) && !has_meta(rhs))
        return unify_status::Failed;
    else if (is_meta(lhs))
        return unify_simple_core(s, lhs, rhs, j);
    else if (is_meta(rhs))
        return unify_simple_core(s, rhs, lhs, j);
    else if (is_succ(lhs) && is_succ(rhs))
        return unify_simple(s, succ_of(lhs), succ_of(rhs), j);
    else
        return unify_status::Unsupported;
}

unify_status unify_simple(substitution & s, constraint const & c) {
    if (is_eq_cnstr(c))
        return unify_simple(s, cnstr_lhs_expr(c), cnstr_rhs_expr(c), c.get_justification());
    else if (is_level_eq_cnstr(c))
        return unify_simple(s, cnstr_lhs_level(c), cnstr_rhs_level(c), c.get_justification());
    else
        return unify_status::Unsupported;
}

static constraint * g_dont_care_cnstr = nullptr;
static unsigned g_group_size = 1u << 28;
constexpr unsigned g_num_groups = 8;
static unsigned g_cnstr_group_first_index[g_num_groups] = { 0, g_group_size, 2*g_group_size, 3*g_group_size, 4*g_group_size, 5*g_group_size, 6*g_group_size, 7*g_group_size};
static unsigned get_group_first_index(cnstr_group g) {
    return g_cnstr_group_first_index[static_cast<unsigned>(g)];
}
static cnstr_group to_cnstr_group(unsigned d) {
    if (d >= g_num_groups)
        d = g_num_groups-1;
    return static_cast<cnstr_group>(d);
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
    typedef pair<constraint, unsigned> cnstr; // constraint + idx
    struct cnstr_cmp {
        int operator()(cnstr const & c1, cnstr const & c2) const {
            return c1.second < c2.second ? -1 : (c1.second == c2.second ? 0 : 1);
        }
    };
    typedef rb_tree<cnstr, cnstr_cmp> cnstr_set;
    typedef rb_tree<unsigned, unsigned_cmp> cnstr_idx_set;
    typedef name_map<cnstr_idx_set> name_to_cnstrs;
    typedef name_map<unsigned> owned_map;
    typedef rb_map<expr, pair<expr, justification>, expr_quick_cmp> expr_map;
    typedef std::shared_ptr<type_checker> type_checker_ptr;
    environment      m_env;
    name_generator   m_ngen;
    substitution     m_subst;
    constraints      m_postponed; // constraints that will not be solved
    owned_map        m_owned_map; // mapping from metavariable name m to delay factor of the choice constraint that owns m
    expr_map         m_type_map;  // auxiliary map for storing the type of the expr in choice constraints
    unifier_plugin   m_plugin;
    type_checker_ptr m_tc;
    type_checker_ptr m_flex_rigid_tc; // type checker used when solving flex rigid constraints. By default,
                                      // only the definitions from the main module are treated as transparent.
    unifier_config   m_config;
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
        constraints      m_postponed;
        cnstr_set        m_cnstrs;
        expr_map         m_type_map;
        name_to_cnstrs   m_mvar_occs;
        owned_map        m_owned_map;

        /** \brief Save unifier's state */
        case_split(unifier_fn & u, justification const & j):
            m_assumption_idx(u.m_next_assumption_idx), m_jst(j), m_subst(u.m_subst),
            m_postponed(u.m_postponed), m_cnstrs(u.m_cnstrs), m_type_map(u.m_type_map),
            m_mvar_occs(u.m_mvar_occs), m_owned_map(u.m_owned_map) {
            u.m_next_assumption_idx++;
        }

        /** \brief Restore unifier's state with saved values, and update m_assumption_idx and m_failed_justifications. */
        void restore_state(unifier_fn & u) {
            lean_assert(u.in_conflict());
            u.m_subst     = m_subst;
            u.m_postponed = m_postponed;
            u.m_cnstrs    = m_cnstrs;
            u.m_mvar_occs = m_mvar_occs;
            u.m_owned_map = m_owned_map;
            u.m_type_map  = m_type_map;
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
        lazy_constraints_case_split(unifier_fn & u, justification const & j, lazy_list<constraints> const & tail):
            case_split(u, j), m_tail(tail) {}
        virtual bool next(unifier_fn & u) { return u.next_lazy_constraints_case_split(*this); }
    };

    struct simple_case_split : public case_split {
        list<constraints> m_tail;
        simple_case_split(unifier_fn & u, justification const & j, list<constraints> const & tail):case_split(u, j), m_tail(tail) {}
        virtual bool next(unifier_fn & u) { return u.next_simple_case_split(*this); }
    };

    struct delta_unfold_case_split : public case_split {
        bool       m_done;
        constraint m_cnstr;
        delta_unfold_case_split(unifier_fn & u, justification const & j, constraint const & c):
            case_split(u, j), m_done(false), m_cnstr(c) {}
        virtual bool next(unifier_fn & u) { return u.next_delta_unfold_case_split(*this); }
    };

    case_split_stack        m_case_splits;
    optional<justification> m_conflict; //!< if different from none, then there is a conflict.

    unifier_fn(environment const & env, unsigned num_cs, constraint const * cs,
               name_generator && ngen, substitution const & s,
               unifier_config const & cfg):
        m_env(env), m_ngen(ngen), m_subst(s), m_plugin(get_unifier_plugin(env)),
        m_config(cfg), m_num_steps(0) {
        switch (m_config.m_kind) {
        case unifier_kind::Cheap:
            m_tc = mk_opaque_type_checker(env, m_ngen.mk_child());
            m_flex_rigid_tc = m_tc;
            m_config.m_computation = false;
            break;
        case unifier_kind::VeryConservative:
            m_tc = mk_type_checker(env, m_ngen.mk_child(), UnfoldReducible);
            m_flex_rigid_tc = m_tc;
            m_config.m_computation = false;
            break;
        case unifier_kind::Conservative:
            m_tc = mk_type_checker(env, m_ngen.mk_child(), UnfoldQuasireducible);
            m_flex_rigid_tc = m_tc;
            m_config.m_computation = false;
            break;
        case unifier_kind::Liberal:
            m_tc = mk_type_checker(env, m_ngen.mk_child());
            if (!cfg.m_computation)
                m_flex_rigid_tc = mk_type_checker(env, m_ngen.mk_child(), UnfoldQuasireducible);
            break;
        default:
            lean_unreachable();
        }
        m_next_assumption_idx = 0;
        m_next_cidx = 0;
        m_first     = true;
        process_input_constraints(num_cs, cs);
    }

    void process_input_constraints(unsigned num_cs, constraint const * cs) {
        // Input choice constraints may have ownership over a metavariable.
        // So, we must first process them, to make sure the ownership table is initialized before
        // we solve the remaining constraints
        for (unsigned i = 0; i < num_cs; i++) {
            if (cs[i].kind() == constraint_kind::Choice)
                preprocess_choice_constraint(cs[i]);
        }
        for (unsigned i = 0; i < num_cs; i++) {
            if (cs[i].kind() != constraint_kind::Choice)
                process_constraint(cs[i]);
        }
    }

    void check_system() {
        ::lean::check_system("unifier");
    }

    void check_full() {
        check_system();
        if (m_num_steps > m_config.m_max_steps)
            throw exception(sstream() << "unifier maximum number of steps (" << m_config.m_max_steps << ") exceeded, " <<
                            "the maximum number of steps can be increased by setting the option unifier.max_steps " <<
                            "(remark: the unifier uses higher order unification and unification-hints, " <<
                            "which may trigger non-termination");
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

    /** \brief For each metavariable m in e add an entry m -> cidx at m_mvar_occs.
        Return true if at least one entry was added.
    */
    bool add_meta_occs(expr const & e, unsigned cidx) {
        bool added = false;
        if (has_expr_metavar(e)) {
            for_each(e, [&](expr const & e, unsigned) {
                    if (is_meta(e)) {
                        add_meta_occ(e, cidx);
                        added = true;
                        return false;
                    }
                    if (is_local(e))
                        return false;
                    return has_expr_metavar(e);
                });
        }
        return added;
    }

    /** \brief Add constraint to the constraint queue */
    unsigned add_cnstr(constraint const & c, cnstr_group g) {
        unsigned cidx = m_next_cidx + get_group_first_index(g);
        m_cnstrs.insert(cnstr(c, cidx));
        m_next_cidx++;
        return cidx;
    }

    /** \brief Check if \c t1 and \c t2 are definitionally equal, if they are not, set a conflict with justification \c j
    */
    bool is_def_eq(expr const & t1, expr const & t2, justification const & j) {
        try {
            auto dcs = m_tc->is_def_eq(t1, t2, j);
            if (!dcs.first) {
                // std::cout << "conflict: " << t1 << " =?= " << t2 << "\n";
                set_conflict(j);
                return false;
            } else {
                return process_constraints(dcs.second);
            }
        } catch (exception&) {
            set_conflict(j);
            return false;
        }
    }

    /** \brief Process the given constraints. Return true iff no conflict was detected. */
    bool process_constraints(constraint_seq const & cs) {
        return cs.all_of([&](constraint const & c) { return process_constraint(c); });
    }

    bool process_constraints(buffer<constraint> const & cs) {
        for (auto const & c : cs) {
            if (!process_constraint(c))
                return false;
        }
        return true;
    }


    /** \brief Process constraints in \c cs, and append justification \c j to them. */
    bool process_constraints(constraint_seq const & cs, justification const & j) {
        return cs.all_of([&](constraint const & c) {
                return process_constraint(update_justification(c, mk_composite1(c.get_justification(), j)));
            });
    }

    template<typename Constraints>
    bool process_constraints(Constraints const & cs, justification const & j) {
        for (auto const & c : cs) {
            if (!process_constraint(update_justification(c, mk_composite1(c.get_justification(), j))))
                return false;
        }
        return true;
    }

    /** \brief Put \c e in weak head normal form.

        \remark Constraints generated in the process are stored in \c cs.
    */
    expr whnf(expr const & e, constraint_seq & cs) {
        return m_tc->whnf(e, cs);
    }

    /** \brief Infer \c e type.

        \remark Return none if an exception was throw when inferring the type.
        \remark Constraints generated in the process are stored in \c cs.
    */
    optional<expr> infer(expr const & e, constraint_seq & cs) {
        try {
            return some_expr(m_tc->infer(e, cs));
        } catch (exception &) {
            return none_expr();
        }
    }

    expr whnf(expr const & e, justification const & j, buffer<constraint> & cs) {
        constraint_seq _cs;
        expr r = whnf(e, _cs);
        to_buffer(_cs, j, cs);
        return r;
    }

    expr flex_rigid_whnf(expr const & e, justification const & j, buffer<constraint> & cs) {
        if (m_config.m_computation) {
            return whnf(e, j, cs);
        } else {
            constraint_seq _cs;
            expr r = m_flex_rigid_tc->whnf(e, _cs);
            to_buffer(_cs, j, cs);
            return r;
        }
    }

    justification mk_assign_justification(expr const & m, expr const & m_type, expr const & v_type, justification const & j) {
        auto r = j.get_main_expr();
        if (!r) r = m;
        justification new_j = mk_justification(r, [=](formatter const & fmt, substitution const & subst, bool) {
                substitution s(subst);
                format r;
                expr _m = s.instantiate(m);
                if (is_meta(_m)) {
                    r = format("type error in placeholder assignment");
                } else {
                    r  = format("type error in placeholder assigned to");
                    r += pp_indent_expr(fmt, _m);
                }
                format expected_fmt, given_fmt;
                std::tie(expected_fmt, given_fmt) = pp_until_different(fmt, m_type, v_type);
                r += compose(line(), format("placeholder has type"));
                r += given_fmt;
                r += compose(line(), format("but is expected to have type"));
                r += expected_fmt;
                r += compose(line(), format("the assignment was attempted when processing"));
                r += nest(2*get_pp_indent(fmt.get_options()), compose(line(), j.pp(fmt, nullptr, subst, false)));
                return r;
            });
        return mk_composite1(new_j, j);
    }

    /**
       \brief Given lhs of the form (m args), assign (m args) := rhs with justification j.
       The type of lhs and rhs are inferred, and is_def_eq is invoked.

       Any other constraint that contains \c m is revisited
    */
    bool assign(expr const & lhs, expr const & m, buffer<expr> const & args, expr const & rhs, justification const & j) {
        lean_assert(is_metavar(m));
        lean_assert(!in_conflict());
        m_subst.assign(m, args, rhs, j);
        constraint_seq cs;
        auto lhs_type = infer(lhs, cs);
        auto rhs_type = infer(rhs, cs);
        if (lhs_type && rhs_type) {
            if (!process_constraints(cs, j))
                return false;
            justification new_j = mk_assign_justification(m, *lhs_type, *rhs_type, j);
            if (!is_def_eq(*lhs_type, *rhs_type, new_j))
                return false;
        } else {
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
        m_subst.assign(m, v, j);
        return true;
    }

    justification mk_invalid_local_ctx_justification(expr const & lhs, expr const & rhs, justification const & j,
                                                     expr const & bad_local) {
        justification new_j = mk_justification(get_app_fn(lhs), [=](formatter const & fmt, substitution const & subst, bool) {
                format r = format("invalid local context when tried to assign");
                r += pp_indent_expr(fmt, rhs);
                buffer<expr> locals;
                auto m = get_app_args(lhs, locals);
                r += line() + format("containing '") + fmt(bad_local) + format("', to placeholder '") + fmt(m) + format("'");
                if (locals.empty()) {
                    r += format(", in the empty local context");
                } else {
                    r += format(", in the local context");
                    format aux;
                    bool first = true;
                    for (expr const l : locals) {
                        if (first) first = false; else aux += space();
                        aux += fmt(l);
                    }
                    r += nest(get_pp_indent(fmt.get_options()), compose(line(), aux));
                }
                r += compose(line(), format("the assignment was attempted when processing"));
                r += nest(2*get_pp_indent(fmt.get_options()), compose(line(), j.pp(fmt, nullptr, subst, false)));
                return r;
            });
        return mk_composite1(new_j, j);
    }

    enum status { Solved, Failed, Continue };

    struct interrupt_normalizer {};

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
        expr bad_local;
        occurs_check_status status;
        if (m_config.m_ignore_context_check)
            status = occurs_check_status::Ok;
        else
            status = occurs_context_check(m_subst, rhs, *m, locals, bad_local);
        if (status == occurs_check_status::FailLocal || status == occurs_check_status::FailCircular) {
            // Try to normalize rhs
            // Example:  ?M := f (pr1 (pair 0 ?M))
            try {
                unsigned counter = 0;
                constraint_seq cs;
                auto is_target_fn = [&](expr const & e) {
                    if ((status == occurs_check_status::FailLocal && occurs(bad_local, e)) ||
                        (status == occurs_check_status::FailCircular && occurs(*m, e))) {
                        counter++;
                        if (counter > m_config.m_normalizer_max_steps)
                            throw interrupt_normalizer();
                        return true;
                    } else {
                        return false;
                    }
                };
                expr rhs_n = normalize(*m_tc, rhs, is_target_fn, cs);
                if (rhs != rhs_n && process_constraints(cs))
                    return process_metavar_eq(lhs, rhs_n, j);
            } catch (interrupt_normalizer &) {
                // exceeded maximum number of steps
            }
        }
        switch (status) {
        case occurs_check_status::FailLocal:
            set_conflict(mk_invalid_local_ctx_justification(lhs, rhs, j, bad_local));
            return Failed;
        case occurs_check_status::FailCircular:
            set_conflict(j);
            return Failed;
        case occurs_check_status::Maybe:
            return Continue;
        case occurs_check_status::Ok:
            lean_assert(!m_subst.is_assigned(*m));
            if (assign(lhs, *m, locals, rhs, j)) {
                return Solved;
            } else {
                return Failed;
            }
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    optional<declaration> is_delta(expr const & e) {
        return m_tc->is_delta(e);
    }

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

    pair<constraint, bool> instantiate_metavars(constraint const & c) {
        if (is_eq_cnstr(c)) {
            auto lhs_jst = m_subst.instantiate_metavars(cnstr_lhs_expr(c));
            auto rhs_jst = m_subst.instantiate_metavars(cnstr_rhs_expr(c));
            expr lhs = lhs_jst.first;
            expr rhs = rhs_jst.first;
            if (lhs != cnstr_lhs_expr(c) || rhs != cnstr_rhs_expr(c)) {
                return mk_pair(mk_eq_cnstr(lhs, rhs,
                                           mk_composite1(mk_composite1(c.get_justification(), lhs_jst.second), rhs_jst.second)),
                               true);
            }
        } else if (is_level_eq_cnstr(c)) {
            auto lhs_jst = m_subst.instantiate_metavars(cnstr_lhs_level(c));
            auto rhs_jst = m_subst.instantiate_metavars(cnstr_rhs_level(c));
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

    expr instantiate_meta(expr e, justification & j) {
        while (true) {
            if (auto p = m_subst.expand_metavar_app(e)) {
                // The following check_system is defensive programming.
                // If the unifier is correct, and no loops are introduced in the substituion,
                // then this loop should always terminate.
                // Anyway, we may have bugs, and we should interrupt the loop if all resources are being consumed.
                check_system();
                e = p->first;
                j = mk_composite1(j, p->second);
            } else {
                return e;
            }
        }
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

    /** \brief Return a delay factor if e is of the form (?m ...) and ?m is a metavariable owned by
        a choice constraint. The delay factor is the delay of the choice constraint.
        Return none otherwise. */
    optional<unsigned> is_owned(expr const & e) {
        expr const & m = get_app_fn(e);
        if (!is_metavar(m))
            return optional<unsigned>();
        if (auto it = m_owned_map.find(mlocal_name(m)))
            return optional<unsigned>(*it);
        else
            return optional<unsigned>();
    }

    /** \brief Applies previous method to the left and right hand sides of the equality constraint */
    optional<unsigned> is_owned(constraint const & c) {
        if (auto d = is_owned(cnstr_lhs_expr(c)))
            return d;
        else
            return is_owned(cnstr_rhs_expr(c));
    }

    static status to_status(bool b) { return b ? Solved : Failed; }

    status reduce_both_proj_and_check(expr const & lhs, expr const & rhs, justification const & j) {
        lean_assert(is_projection_app(lhs));
        lean_assert(is_projection_app(rhs));
        constraint_seq new_cs;
        expr new_lhs = whnf(lhs, new_cs);
        expr new_rhs = whnf(rhs, new_cs);
        if (lhs != new_lhs || rhs != new_rhs)
            return to_status(is_def_eq(new_lhs, new_rhs, j) && process_constraints(new_cs));
        if (const_name(get_app_fn(lhs)) != const_name(get_app_fn(rhs))) {
            // Two projection applications
            //     pr_1 ... =?= pr_2 ...
            // where pr_1 != pr_2 and both are not stuck
            set_conflict(j);
            return Failed;
        } else {
            return Continue;
        }
    }

    status reduce_proj_and_check(expr const & lhs, expr const & rhs, justification const & j) {
        lean_assert(is_projection_app(lhs));
        lean_assert(!is_projection_app(rhs));
        {
            // First try to reduce projection
            constraint_seq new_cs;
            expr new_lhs = whnf(lhs, new_cs);
            if (lhs != new_lhs)
                return to_status(is_def_eq(new_lhs, rhs, j) && process_constraints(new_cs));
        }
        {
            constraint_seq new_cs;
            expr new_rhs = whnf(rhs, new_cs);
            if (rhs != new_rhs)
                return to_status(is_def_eq(lhs, new_rhs, j) && process_constraints(new_cs));
        }
        return Continue;
    }

    /** \brief Process an equality constraints. */
    bool process_eq_constraint(constraint const & c) {
        lean_assert(is_eq_cnstr(c));
        // instantiate assigned metavariables
        status st = instantiate_eq_cnstr(c);
        if (st != Continue) return st == Solved;

        if (auto d = is_owned(c)) {
            // Metavariable in the constraint is owned by choice constraint.
            // So, we postpone this constraint.
            add_cnstr(c, to_cnstr_group(*d+1));
            return true;
        }

        st = process_eq_constraint_core(c);
        if (st != Continue) return st == Solved;

        expr const & lhs = cnstr_lhs_expr(c);
        expr const & rhs = cnstr_rhs_expr(c);
        bool is_proj_lhs = is_projection_app(lhs);
        bool is_proj_rhs = is_projection_app(rhs);
        bool is_proj_stuck_lhs = is_proj_lhs && m_tc->is_stuck(lhs);
        bool is_proj_stuck_rhs = is_proj_rhs && m_tc->is_stuck(rhs);

        if (is_proj_lhs && is_proj_rhs && !is_proj_stuck_lhs && !is_proj_stuck_rhs) {
            if (const_name(get_app_fn(lhs)) == const_name(get_app_fn(rhs))) {
                return process_same_projection_projection(c);
            } else {
                st = reduce_both_proj_and_check(lhs, rhs, c.get_justification());
                if (st != Continue) return st == Solved;
            }
        } else if (is_proj_lhs && !is_proj_stuck_lhs && !is_proj_rhs && !is_meta(rhs)) {
            st = reduce_proj_and_check(lhs, rhs, c.get_justification());
            if (st != Continue) return st == Solved;
        } else if (is_proj_rhs && !is_proj_stuck_rhs && !is_proj_lhs && !is_meta(lhs)) {
            st = reduce_proj_and_check(rhs, lhs, c.get_justification());
            if (st != Continue) return st == Solved;
        }

        if (is_eq_deltas(lhs, rhs)) {
            // we need to create a backtracking point for this one
            add_cnstr(c, cnstr_group::Basic);
            return true;
        } else if (is_meta(lhs) && is_meta(rhs)) {
            // flex-flex constraints are delayed the most.
            unsigned cidx = add_cnstr(c, cnstr_group::FlexFlex);
            add_meta_occ(lhs, cidx);
            add_meta_occ(rhs, cidx);
            return true;
        } else if (m_tc->may_reduce_later(lhs) ||
                   m_tc->may_reduce_later(rhs) ||
                   m_plugin->delay_constraint(*m_tc, c)) {
            unsigned cidx = add_cnstr(c, cnstr_group::PluginDelayed);
            add_meta_occs(lhs, cidx);
            add_meta_occs(rhs, cidx);
            if (is_proj_lhs && is_proj_rhs)
                return preprocess_projection_projection(c);
            else
                return true;
        } else if (is_meta(lhs)) {
            // flex-rigid constraints are delayed.
            unsigned cidx = add_cnstr(c, cnstr_group::FlexRigid);
            add_meta_occ(lhs, cidx);
            return true;
        } else if (is_meta(rhs)) {
            // flex-rigid constraints are delayed.
            unsigned cidx = add_cnstr(c, cnstr_group::FlexRigid);
            add_meta_occ(rhs, cidx);
            return true;
        } else {
            // this constraints require the unifier plugin to be solved
            add_cnstr(c, cnstr_group::Basic);
            return true;
        }
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
            if (is_succ(rhs)) {
                set_conflict(j);
                return Failed;
            } else {
                return Continue;
            }
        }
        lean_assert(!m_subst.is_assigned(lhs));
        if (assign(lhs, rhs, j)) {
            return Solved;
        } else {
            set_conflict(j);
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

        if (lhs != cnstr_lhs_level(new_c) || rhs != cnstr_rhs_level(new_c))
            new_c = mk_level_eq_cnstr(lhs, rhs, new_c.get_justification());

        add_cnstr(new_c, cnstr_group::FlexRigid);
        return true;
    }

    bool preprocess_choice_constraint(constraint c) {
        if (!cnstr_on_demand(c)) {
            if (cnstr_is_owner(c)) {
                expr m = get_app_fn(cnstr_expr(c));
                lean_assert(is_metavar(m));
                m_owned_map.insert(mlocal_name(m), cnstr_delay_factor(c));
            }
            add_cnstr(c, get_choice_cnstr_group(c));
            return true;
        } else {
            expr m = cnstr_expr(c);
            // choice constraints that are marked as "on demand"
            // are only processed when all metavariables in the
            // type of m have been instantiated.
            expr type;
            justification jst;
            if (auto it = m_type_map.find(m)) {
                // Type of m is already cached in m_type_map
                type = it->first;
                jst  = it->second;
            } else {
                // Type of m is not cached yet, we
                // should infer it, process generated
                // constraints and save the result in
                // m_type_map.
                constraint_seq cs;
                optional<expr> t = infer(m, cs);
                if (!t) {
                    set_conflict(c.get_justification());
                    return false;
                }
                if (!process_constraints(cs, c.get_justification()))
                    return false;
                type = *t;
                m_type_map.insert(m, mk_pair(type, justification()));
            }
            // Try to instantiate metavariables in type
            pair<expr, justification> type_jst = m_subst.instantiate_metavars(type);
            if (type_jst.first != type) {
                // Type was modified by instantiation,
                // we update the constraint justification,
                // and store the new type in m_type_map
                jst  = mk_composite1(jst, type_jst.second);
                type = type_jst.first;
                c    = update_justification(c, mk_composite1(c.get_justification(), jst));
                m_type_map.insert(m, mk_pair(type, jst));
            }
            unsigned cidx = add_cnstr(c, cnstr_group::ClassInstance);
            if (!add_meta_occs(type, cidx)) {
                // type does not contain metavariables...
                // so this "on demand" constraint is ready to be solved
                m_cnstrs.erase(cnstr(c, cidx));
                add_cnstr(c, cnstr_group::Basic);
                m_type_map.erase(m);
            }
            return true;
        }
    }

    /**
        \brief Process the given constraint \c c. "Easy" constraints are solved, and the remaining ones
        are added to the constraint queue m_cnstrs. By "easy", see the methods
        #process_eq_constraint and #process_level_eq_constraint.
    */
    bool process_constraint(constraint const & c) {
        if (in_conflict())
            return false;
        check_full();
        // std::cout << "process: " << c << "\n";
        switch (c.kind()) {
        case constraint_kind::Choice:
            return preprocess_choice_constraint(c);
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
        cnstr c(*g_dont_care_cnstr, cidx);
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
        out << j.pp(mk_print_formatter_factory()(m_env, options()), nullptr, m_subst) << "\n";
        if (j.is_composite()) {
            display(out, composite_child1(j), indent+2);
            display(out, composite_child2(j), indent+2);
        }
    }

    void pop_case_split() {
        m_case_splits.pop_back();
    }

    bool resolve_conflict() {
        lean_assert(in_conflict());
        while (!m_case_splits.empty()) {
            check_system();
            justification conflict = *m_conflict;
            std::unique_ptr<case_split> & d = m_case_splits.back();
            if (!m_config.m_nonchronological || depends_on(conflict, d->m_assumption_idx)) {
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

    /** \brief Given a constraint of the form
            f a_1 ... a_n =?= f b_1 ... b_n
        Return singleton stream with the possible solution
             a_i =?= b_i
        If c is not of the expected form, then return the empty stream.
    */
    lazy_list<constraints> process_const_const_cnstr(constraint const & c) {
        if (!is_eq_cnstr(c))
            return lazy_list<constraints>();
        expr const & lhs = cnstr_lhs_expr(c);
        expr const & rhs = cnstr_rhs_expr(c);
        expr const & f_lhs = get_app_fn(lhs);
        expr const & f_rhs = get_app_fn(rhs);
        if (!is_constant(f_lhs) || !is_constant(f_rhs) || const_name(f_lhs) != const_name(f_rhs))
            return lazy_list<constraints>();
        justification const & j = c.get_justification();
        constraint_seq cs;
        auto fcs = m_tc->is_def_eq(f_lhs, f_rhs, j);
        if (!fcs.first)
            return lazy_list<constraints>();
        cs = fcs.second;
        buffer<expr> args_lhs, args_rhs;
        get_app_args(lhs, args_lhs);
        get_app_args(rhs, args_rhs);
        if (args_lhs.size() != args_rhs.size())
            return lazy_list<constraints>();
        for (unsigned i = 0; i < args_lhs.size(); i++) {
            auto acs = m_tc->is_def_eq(args_lhs[i], args_rhs[i], j);
            if (!acs.first)
                return lazy_list<constraints>();
            cs = acs.second + cs;
        }
        return lazy_list<constraints>(cs.to_list());
    }

    /** Return true iff t is a projection application */
    bool is_projection_app(expr const & t) {
        expr const & f = get_app_fn(t);
        return is_constant(f) && is_projection(m_env, const_name(f));
    }

    // See #preprocess_projection_projection
    bool is_preprocess_projection_projection_target(projection_info const * info, buffer<expr> const & args) {
        if (!info->m_inst_implicit)
            return false;
        if (args.size() < info->m_nparams+1)
            return false;
        unsigned sidx = info->m_nparams;
        if (!has_expr_metavar(args[sidx]))
            return false;
        for (unsigned i = 0; i < info->m_nparams; i++)
            if (has_expr_metavar(args[i]))
                return true;
        // all parameters do not have metavariables, thus type class resolution will be triggered
        // to synthesize the args[sidx]
        return false;
    }

    /**
      For constraints of the form
        pr_1 A_1 s_1 a_1 =?= pr_2 A_2 s_2 a_2
      where pr is a projection, A_{1,2} are parameters, s_{1,2} the structure, and a_{1,2} arguments.
      If s_1/A_1 or s_2/A_2 contain metavariables, we add the constraint
          infer_type(pr_1 A_1 s_1) =?= infer_type(pr_2 A_2 s_2)
      when pr_{1,2} is the projection of a class. The new constraint may force some of the meta-variables occurring
      in the parameters to be assigned, and then this assignment will trigger type class resolution at s_{1,2}

      \remark Note that whenever we use this step we may be missing solutions.
      This should only happen in very unusual circumstances. We may add an option to disable this
      step in the future. This step is essential for processing the algebraic hierarchy.
    */
    bool preprocess_projection_projection(constraint const & c) {
        expr const & lhs = cnstr_lhs_expr(c);
        expr const & rhs = cnstr_rhs_expr(c);
        lean_assert(is_projection_app(lhs) && is_projection_app(rhs));
        buffer<expr> lhs_args, rhs_args;
        expr const & f_lhs = get_app_args(lhs, lhs_args);
        expr const & f_rhs = get_app_args(rhs, rhs_args);
        projection_info const * info_lhs = get_projection_info(m_env, const_name(f_lhs));
        projection_info const * info_rhs = get_projection_info(m_env, const_name(f_rhs));
        lean_assert(info_lhs);
        lean_assert(info_rhs);
        if (!is_preprocess_projection_projection_target(info_lhs, lhs_args) &&
            !is_preprocess_projection_projection_target(info_rhs, rhs_args))
            return true; // do nothing, preprocessing step will not help
        unsigned l_nparams = info_lhs->m_nparams;
        unsigned r_nparams = info_rhs->m_nparams;
        if (lhs_args.size() - l_nparams != rhs_args.size() - r_nparams)
            return true; // the number of arguments to the projection data do not match.
        expr new_lhs_app = mk_app(f_lhs, l_nparams+1, lhs_args.data());
        expr new_rhs_app = mk_app(f_rhs, r_nparams+1, rhs_args.data());
        constraint_seq cs;
        auto t1 = infer(new_lhs_app, cs);
        auto t2 = infer(new_rhs_app, cs);
        if (!t1 || !t2)
            return true; // failed to infer types
        if (!process_constraints(cs))
            return false;
        return is_def_eq(*t1, *t2, c.get_justification());
    }

    /** \brief Return true iff lhs and rhs are of the form (pr ...) where pr is a projection */
    bool is_same_projection_projection(expr const & lhs, expr const & rhs) {
        expr const & f_lhs = get_app_fn(lhs);
        expr const & f_rhs = get_app_fn(rhs);
        return
            is_constant(f_lhs) && is_constant(f_rhs) &&
            const_name(f_lhs) == const_name(f_rhs) &&
            is_projection(m_env, const_name(f_lhs));
    }

    /** \brief Return true iff c is of the form (pr ...) =?= (pr ...) where pr is a projection. */
    bool is_same_projection_projection(constraint const & c) {
        lean_assert(is_eq_cnstr(c));
        return is_same_projection_projection(cnstr_lhs_expr(c), cnstr_rhs_expr(c));
    }

    /**
       \brief Reduce constraint
           pr a_1 ... a_n =?= pr b_1 ... b_n
       into
           a_1 =?= b_1, ..., a_n =?= b_n
       where pr is a projection

       \remark This step is only performed at process_next.
       Moreover, we only do it when the "major premise" of both projections is not a constructor.
    */
    bool process_same_projection_projection(constraint const & c) {
        lean_assert(is_same_projection_projection(c));
        buffer<expr> lhs_args, rhs_args;
        expr const & f_lhs = get_app_args(cnstr_lhs_expr(c), lhs_args);
        expr const & f_rhs = get_app_args(cnstr_rhs_expr(c), rhs_args);
        justification const & j = c.get_justification();
        return process_levels(const_levels(f_lhs), const_levels(f_rhs), j) && process_args(lhs_args, rhs_args, j);
    }

    /** \brief Return true iff c is of the form (pr_1 ...) =?= (pr_2 ...) where pr_1 and pr_2 are projections. */
    bool is_projection_projection(constraint const & c) {
        return is_projection_app(cnstr_lhs_expr(c)) && is_projection_app(cnstr_rhs_expr(c));
    }

    /**
       \brief Postpone constraints of the form
           pr_1 a_1 ... a_n =?= pr_2 b_1 ... b_m
       when pr_1 and pr_2 are projections and pr_1 != pr_2

       If the constraint cannot be postponed anymore, we just fail.

       \remark This step is only performed at process_next.
    */
    bool process_projection_projection(constraint const & c, unsigned cidx) {
        lean_assert(is_projection_projection(c));
        // postpone constraint
        if (cidx < get_group_first_index(cnstr_group::ClassInstance)) {
            // pospone constraint
            unsigned cidx = add_cnstr(c, cnstr_group::Epilogue);
            add_meta_occs(cnstr_lhs_expr(c), cidx);
            add_meta_occs(cnstr_rhs_expr(c), cidx);
            return true;
        } else {
            set_conflict(c.get_justification());
            return false;
        }
    }

    /** \brief Return true iff c is of the form (pr ...) =?= t, where
        pr is a stuck projection. */
    bool is_projection_lhs(constraint const & c) {
        lean_assert(is_eq_cnstr(c));
        return is_projection_app(cnstr_lhs_expr(c)) && m_tc->is_stuck(cnstr_lhs_expr(c));
    }

    /** \brief Return true iff c is of the form t =?= (pr ...), where
        pr is a stuck projection. */
    bool is_projection_rhs(constraint const & c) {
        lean_assert(is_eq_cnstr(c));
        return is_projection_app(cnstr_rhs_expr(c)) && m_tc->is_stuck(cnstr_rhs_expr(c));
    }

    /** \brief Process constraints of the form
                   (pr_i ... M ..) =?= t
        If the "major premise" M of (pr_i ... M ...) is stuck, we reduce the constraint above into
                   M =?= (mk ?M_1 ... ?M_k)
                   (?M_i ...) =?= t
        where ?M_i's are fresh metavariables

        If M is not stuck, the procedure signs a conflict

        \remark This step is only performed at process_next.
    */
    bool process_projection_eq(expr const & lhs, expr const & rhs, justification const & j) {
        lean_assert(is_projection_app(lhs));
        buffer<expr> pr_args;
        expr const & pr = get_app_args(lhs, pr_args);
        projection_info const * info = get_projection_info(m_env, const_name(pr));
        unsigned nparams = info->m_nparams;
        unsigned mkidx   = nparams;
        if (pr_args.size() < nparams+1) {
            set_conflict(j);
            return false;
        }
        auto stuck_it = m_tc->is_stuck(pr_args[mkidx]);
        if (!stuck_it) {
            // TODO(Lean): normalize, and try is_stuck again?
            // We don't do it because it seems there is very little gain, and it may negatively affect performance.
            return false;
        }
        expr meta = *stuck_it;
        lean_assert(is_meta(meta));
        buffer<expr> meta_args;
        expr const & mvar      = get_app_args(meta, meta_args);
        expr const & mvar_type = mlocal_type(mvar);
        constraint_seq cs;
        expr mk = mk_app(mk_constant(info->m_constructor, const_levels(pr)), nparams, pr_args.data());
        auto it = infer(mk, cs);
        if (!it) {
            set_conflict(j);
            return false;
        }
        // Remark: this is another example where it would be really nice if every
        // unification constraint had a context associated with it.
        expr mk_type = whnf(*it, cs);
        optional<expr> mk_i;
        unsigned i = 0;
        while (is_pi(mk_type)) {
            expr new_mvar = mk_app(mk_aux_metavar_for(m_ngen, mvar_type), meta_args);
            mk = mk_app(mk, new_mvar);
            if (info->m_i == i)
                mk_i = new_mvar;
            i++;
            mk_type = whnf(instantiate(binding_body(mk_type), new_mvar), cs);
        }
        if (!mk_i) {
            set_conflict(j);
            return false;
        }
        expr Mi = mk_app(*mk_i, pr_args.size() - mkidx - 1, pr_args.data() + mkidx + 1);
        cs += mk_eq_cnstr(meta, mk, j);
        cs += mk_eq_cnstr(Mi, rhs, j);
        return process_constraints(cs);
    }

    bool process_plugin_constraint(constraint const & c) {
        lean_assert(!is_choice_cnstr(c));
        lazy_list<constraints> alts = m_plugin->solve(*m_tc, c, m_ngen.mk_child());
        alts = append(alts, process_const_const_cnstr(c));
        return process_lazy_constraints(alts, c.get_justification());
    }

    bool process_choice_constraint(constraint const & c) {
        lean_assert(is_choice_cnstr(c));
        expr const &   m            = cnstr_expr(c);
        choice_fn const & fn        = cnstr_choice_fn(c);
        if (cnstr_is_owner(c)) {
            // choice will have a chance to assign m, so
            // we remove the "barrier" that was preventing m from being assigned.
            m_owned_map.erase(mlocal_name(get_app_fn(m)));
        }
        expr m_type;

        constraint_seq cs;
        if (auto type = infer(m, cs)) {
            m_type = *type;
            if (!process_constraints(cs))
                return false;
        } else {
            set_conflict(c.get_justification());
            return false;
        }
        auto m_type_jst             = m_subst.instantiate_metavars(m_type);
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

    bool unfold_delta(constraint const & c, justification const & extra_j) {
        expr const & lhs = cnstr_lhs_expr(c);
        expr const & rhs = cnstr_rhs_expr(c);
        buffer<expr> lhs_args, rhs_args;
        justification j = c.get_justification();
        expr lhs_fn     = get_app_rev_args(lhs, lhs_args);
        expr rhs_fn     = get_app_rev_args(rhs, rhs_args);
        declaration d   = *m_env.find(const_name(lhs_fn));
        expr lhs_fn_val = instantiate_value_univ_params(d, const_levels(lhs_fn));
        expr rhs_fn_val = instantiate_value_univ_params(d, const_levels(rhs_fn));
        expr t = apply_beta(lhs_fn_val, lhs_args.size(), lhs_args.data());
        expr s = apply_beta(rhs_fn_val, rhs_args.size(), rhs_args.data());
        auto dcs = m_tc->is_def_eq(t, s, j);
        if (dcs.first) {
            constraints cnstrs = dcs.second.to_list();
            return process_constraints(cnstrs, extra_j);
        } else {
            set_conflict(j);
            return false;
        }
    }

    bool next_delta_unfold_case_split(delta_unfold_case_split & cs) {
        if (!cs.m_done) {
            cs.restore_state(*this);
            cs.m_done = true;
            constraint const & c = cs.m_cnstr;
            justification j      = mk_composite1(cs.get_jst(), mk_assumption_justification(cs.m_assumption_idx));
            return unfold_delta(c, j);
        } else {
            // update conflict
            update_conflict(mk_composite1(*m_conflict, cs.m_failed_justifications));
            pop_case_split();
            return false;
        }
    }

    // Make sure the two lists of levels are definitionally equal.
    bool process_levels(levels lhs_lvls, levels rhs_lvls, justification const & j) {
        while (!is_nil(lhs_lvls)) {
            if (is_nil(rhs_lvls))
                return false;
            level lhs = head(lhs_lvls);
            level rhs = head(rhs_lvls);
            if (!process_constraint(mk_level_eq_cnstr(lhs, rhs, j)))
                return false;
            lhs_lvls = tail(lhs_lvls);
            rhs_lvls = tail(rhs_lvls);
        }
        return is_nil(rhs_lvls);
    }

    // Make sure the two buffers of arguments are definitionally equal
    bool process_args(buffer<expr> const & lhs_args, buffer<expr> const & rhs_args, justification const & j) {
        if (lhs_args.size() != rhs_args.size())
            return false;
        unsigned i = lhs_args.size();
        while (i > 0) {
            --i;
            if (!is_def_eq(lhs_args[i], rhs_args[i], j))
                return false;
        }
        return true;
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
        levels rhs_lvls = const_levels(rhs_fn);
        if (length(lhs_lvls) != length(rhs_lvls) ||
            d.get_num_univ_params() != length(lhs_lvls)) {
            // the constraint is not well-formed, this can happen when users are abusing the API
            set_conflict(j);
            return false;
        }

        if (lhs_args.size() != rhs_args.size())
            return unfold_delta(c, justification());

        justification a;
        if (m_config.m_kind == unifier_kind::Liberal &&
            (m_config.m_computation || module::is_definition(m_env, d.get_name()) || is_at_least_quasireducible(m_env, d.get_name()))) {
            // add case_split for t =?= s
            a = mk_assumption_justification(m_next_assumption_idx);
            add_case_split(std::unique_ptr<case_split>(new delta_unfold_case_split(*this, j, c)));
        }

        // process first case
        justification new_j = mk_composite1(j, a);
        return process_levels(lhs_lvls, rhs_lvls, new_j) && process_args(lhs_args, rhs_args, new_j);
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

    /** \brief Append the auxiliary constraints \c aux to each alternative in \c alts */
    void append_auxiliary_constraints(buffer<constraints> & alts, list<constraint> const & aux) {
        if (is_nil(aux))
            return;
        for (constraints & cs : alts)
            cs = append(aux, cs);
    }

    /** \see ensure_sufficient_args */
    expr ensure_sufficient_args_core(expr mtype, unsigned nargs, unsigned i, constraint_seq & cs) {
        if (i == nargs)
            return mtype;
        mtype = m_tc->ensure_pi(mtype, cs);
        expr local = mk_local_for(mtype);
        expr body  = instantiate(binding_body(mtype), local);
        return Pi(local, ensure_sufficient_args_core(body, nargs, i+1, cs));
    }

    /** \brief Make sure mtype is a Pi of size at least nargs.
        If it is not, we use ensure_pi and (potentially) add new constaints to enforce it.
    */
    expr ensure_sufficient_args(expr const & mtype, unsigned nargs, constraint_seq & cs) {
        expr t = mtype;
        unsigned num = 0;
        while (is_pi(t)) {
            num++;
            t = binding_body(t);
        }
        if (num >= nargs)
            return mtype;
        return ensure_sufficient_args_core(mtype, nargs, 0, cs);
    }

    /** \brief Auxiliary functional object for implementing process_flex_rigid_core */
    class flex_rigid_core_fn {
        unifier_fn &          u;
        expr const &          lhs;
        buffer<expr>          margs;
        expr const &          m;
        expr const &          rhs;
        justification         j;
        buffer<constraints> & alts; // result: alternatives
        bool                  imitation_only; // if true, then only imitation step is used

        optional<bool>        _has_meta_args;

        bool cheap() const { return u.m_config.m_kind == unifier_kind::Cheap; }
        bool pattern() const { return u.m_config.m_pattern; }

        type_checker & tc() {
            return *u.m_tc;
        }

        type_checker & restricted_tc() {
            if (u.m_config.m_computation)
                return *u.m_tc;
            else
                return *u.m_flex_rigid_tc;
        }

        /** \brief Return true if margs contains an expression \c e s.t. is_meta(e) */
        bool has_meta_args() {
            if (!_has_meta_args) {
                _has_meta_args = std::any_of(margs.begin(), margs.end(),
                                              [](expr const & e) { return is_meta(e); });
            }
            return *_has_meta_args;
        }

        /**
           \brief Given t
           <tt>Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), B[x_1, ..., x_n]</tt>
           return
           <tt>fun (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), v[x_1, ... x_n]</tt>

           \remark v has free variables.
        */
        expr mk_lambda_for(unsigned i, expr const & t, expr const & v) {
            if (i < margs.size()) {
                return mk_lambda(binding_name(t), binding_domain(t), mk_lambda_for(i+1, binding_body(t), v), binding_info(t));
            } else {
                return v;
            }
        }

        expr mk_lambda_for(expr const & t, expr const & v) {
            return mk_lambda_for(0, t, v);
        }

        /** \brief Return true if \c local occurs once in the buffer \c es. */
        bool local_occurs_once(expr const & local, buffer<expr> const & es) {
            bool found = false;
            for (expr const & e : es) {
                if (is_local(e) && mlocal_name(e) == mlocal_name(local)) {
                    if (found)
                        return false;
                    found = true;
                }
            }
            return true;
        }

        /** \brief Make sure mtype is a Pi of size at least margs.size(). */
        expr ensure_sufficient_args(expr const & mtype, constraint_seq & cs) {
            return u.ensure_sufficient_args(mtype, margs.size(), cs);
        }

        /**
           \brief Given
                 m      := a metavariable ?m
                 rhs    := sort, constant
           Then solve (?m a_1 ... a_k) =?= rhs, by returning the constraint
                 ?m  =?= fun (x1 ... x_k), rhs
        */
        void mk_simple_imitation() {
            lean_assert(is_metavar(m));
            lean_assert(is_sort(rhs) || is_constant(rhs));
            expr const & mtype = mlocal_type(m);
            constraint_seq cs;
            expr new_mtype = ensure_sufficient_args(mtype, cs);
            cs = cs + mk_eq_cnstr(m, mk_lambda_for(new_mtype, rhs), j);
            alts.push_back(cs.to_list());
        }

        bool restricted_is_def_eq(expr const & marg, expr const & rhs, justification const & j, constraint_seq & cs) {
            try {
                if (restricted_tc().is_def_eq(marg, rhs, j, cs)) {
                    return true;
                } else {
                    return false;
                }
            } catch (exception & ex) {
                return false;
            }
        }

        /**
           Given,
               m      := a metavariable ?m
               margs  := [a_1 ... a_k]
           We say a unification problem (?m a_1 ... a_k) =?= rhs uses "simple nonlocal i-th projection" when

           1) rhs is not a local constant
           2) is_def_eq(a_i, rhs) does not fail

           In this case, we add
                a_i =?= rhs
                ?m  =?= fun x_1 ... x_k, x_i
           to alts as a possible solution.
        */
        void mk_simple_nonlocal_projection(unsigned i) {
            expr const & mtype = mlocal_type(m);
            unsigned vidx = margs.size() - i - 1;
            expr const & marg = margs[i];
            constraint_seq cs;
            auto new_mtype = ensure_sufficient_args(mtype, cs);
            // Remark: we should not use mk_eq_cnstr(marg, rhs, j) since is_def_eq may be able to reduce them.
            // The unifier assumes the eq constraints are reduced.
            if (tc().is_def_eq_types(marg, rhs, j, cs) &&
                restricted_is_def_eq(marg, rhs, j, cs)) {
                expr v = mk_lambda_for(new_mtype, mk_var(vidx));
                cs = cs + mk_eq_cnstr(m, v, j);
                alts.push_back(cs.to_list());
            }
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
        void mk_simple_projections() {
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
                    mk_simple_nonlocal_projection(i);
                    if (cheap())
                        return;
                } else if (is_local(marg) && is_local(rhs) && mlocal_name(marg) == mlocal_name(rhs)) {
                    // if the argument is local, and rhs is equal to it, then we also add a projection
                    constraint_seq cs;
                    auto new_mtype = ensure_sufficient_args(mtype, cs);
                    expr v = mk_lambda_for(new_mtype, mk_var(vidx));
                    cs = cs + mk_eq_cnstr(m, v, j);
                    alts.push_back(cs.to_list());
                    if (cheap())
                        return;
                }
            }
        }

        void mk_app_projections() {
            lean_assert(is_metavar(m));
            lean_assert(is_app(rhs));
            if (!pattern() && !cheap()) {
                expr const & f = get_app_fn(rhs);
                lean_assert(is_constant(f) || is_local(f));
                if (is_local(f)) {
                    unsigned i = margs.size();
                    while (i > 0) {
                        --i;
                        if (!(is_local(margs[i]) && mlocal_name(margs[i]) == mlocal_name(f)))
                            mk_simple_nonlocal_projection(i);
                    }
                } else {
                    mk_simple_projections();
                }
            }
        }

        /** \brief Create the local context \c locals for the imitation step.
         */
        void mk_local_context(buffer<expr> & locals, constraint_seq & cs) {
            expr mtype     = mlocal_type(m);
            unsigned nargs = margs.size();
            mtype = ensure_sufficient_args(mtype, cs);
            expr it = mtype;
            for (unsigned i = 0; i < nargs; i++) {
                expr d     = instantiate_rev(binding_domain(it), locals.size(), locals.data());
                auto d_jst = u.m_subst.instantiate_metavars(d);
                d = d_jst.first;
                j = mk_composite1(j, d_jst.second);
                name n;
                if (is_local(margs[i]) && local_occurs_once(margs[i], margs)) {
                    n = mlocal_name(margs[i]);
                } else {
                    n = u.m_ngen.next();
                }
                expr local = mk_local(n, binding_name(it), d, binding_info(it));
                locals.push_back(local);
                it = binding_body(it);
            }
        }

        expr mk_imitation_arg(expr const & arg, expr const & type, buffer<expr> const & locals,
                               constraint_seq & cs) {
            // The following optimization is broken. It does not really work when we have dependent
            // types. The problem is that the type of arg may depend on other arguments,
            // and constraints are not generated to enforce it.
            //
            //  Here is a minimal counterexample
            //     ?M A B a b H B b  =?=  heq.type_eq A B a b H
            //  with this optimization the imitation is
            //
            //    ?M := fun (A B a b H B' b'), heq.type_eq A (?M1 A B a b H B' b') a (?M2 A B a b H B' b') H
            //
            //  This imitation is only correct if
            //     typeof(H) is (heq A a (?M1 A B a b H B' b') (?M2 A B a b H B' b'))
            //
            //  Adding an extra constraint is problematic since typeof(H) may contain local constants,
            //  and these local constants may have been "renamed" by mk_local_context above
            //
            //  For now, we simply comment the optimization.
            //

            // Broken optimization
            // if (!has_meta_args() && is_local(arg) && contains_local(arg, locals)) {
            //    return arg;
            // }

            // The following code is not affected by the problem above because we
            // attach the type \c type to the new metavariables being created.

            // std::cout << "type: " << type << "\n";
            if (context_check(type, locals)) {
                expr maux    = mk_metavar(u.m_ngen.next(), Pi(locals, type));
                // std::cout << "  >> " << maux << " : " << mlocal_type(maux) << "\n";
                cs = mk_eq_cnstr(mk_app(maux, margs), arg, j) + cs;
                return mk_app(maux, locals);
            } else {
                expr maux_type   = mk_metavar(u.m_ngen.next(), Pi(locals, mk_sort(mk_meta_univ(u.m_ngen.next()))));
                expr maux        = mk_metavar(u.m_ngen.next(), Pi(locals, mk_app(maux_type, locals)));
                cs = mk_eq_cnstr(mk_app(maux, margs), arg, j) + cs;
                return mk_app(maux, locals);
            }
        }

        void mk_app_imitation_core(expr const & f, buffer<expr> const & locals, constraint_seq & cs) {
            buffer<expr> rargs;
            get_app_args(rhs, rargs);
            buffer<expr> sargs;
            try {
                expr f_type = tc().infer(f, cs);
                for (expr const & rarg : rargs) {
                    f_type      = tc().ensure_pi(f_type, cs);
                    expr d_type = binding_domain(f_type);
                    expr sarg   = mk_imitation_arg(rarg, d_type, locals, cs);
                    sargs.push_back(sarg);
                    f_type      = instantiate(binding_body(f_type), sarg);
                }
            } catch (exception&) {}
            expr v = Fun(locals, mk_app(f, sargs));
            cs += mk_eq_cnstr(m, v, j);
            alts.push_back(cs.to_list());
        }

        /**
           \brief Given
               m      := a metavariable ?m
               margs  := [a_1 ... a_k]
               rhs    := (f b_1 ... b_n)
           Then create the constraints
               (?m_1 a_1 ... a_k) =?= b_1
               ...
               (?m_n a_1 ... a_k) =?= b_n
               ?m  =?= fun (x_1 ... x_k), g (?m_1 x_1 ... x_k) ... (?m_n x_1 ... x_k)

           If f is a constant (or a macro), then g is f.
           If f is a local constant, then we consider each a_i that is equal to f.

           Remark: we try to minimize the number of constraints (?m_i a_1 ... a_k) =?= b_i by detecting "easy" cases
           that can be solved immediately. See \c mk_imitation_arg
        */
        void mk_app_imitation() {
            lean_assert(is_metavar(m));
            lean_assert(is_app(rhs));
            buffer<expr> locals;
            constraint_seq cs;
            flet<justification> let(j, j); // save j value
            mk_local_context(locals, cs);
            lean_assert(margs.size() == locals.size());
            expr const & f = get_app_fn(rhs);
            lean_assert(is_constant(f) || is_macro(f) || is_local(f));
            if (is_local(f)) {
                unsigned i = margs.size();
                while (i > 0) {
                    --i;
                    if (is_local(margs[i]) && mlocal_name(margs[i]) == mlocal_name(f)) {
                        constraint_seq new_cs = cs;
                        mk_app_imitation_core(locals[i], locals, new_cs);
                    }
                }
            } else {
                lean_assert(is_constant(f) || is_macro(f));
                mk_app_imitation_core(f, locals, cs);
            }
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
        void mk_bindings_imitation() {
            lean_assert(is_metavar(m));
            lean_assert(is_binding(rhs));
            constraint_seq cs;
            buffer<expr> locals;
            flet<justification> let(j, j); // save j value
            mk_local_context(locals, cs);
            lean_assert(margs.size() == locals.size());
            try {
                // create a scope to make sure no constraints "leak" into the current state
                expr rhs_A     = binding_domain(rhs);
                expr A_type    = tc().infer(rhs_A, cs);
                expr A         = mk_imitation_arg(rhs_A, A_type, locals, cs);
                expr local     = mk_local(u.m_ngen.next(), binding_name(rhs), A, binding_info(rhs));
                locals.push_back(local);
                margs.push_back(local);
                expr rhs_B     = instantiate(binding_body(rhs), local);
                expr B_type    = tc().infer(rhs_B, cs);
                expr B         = mk_imitation_arg(rhs_B, B_type, locals, cs);
                expr binding   = is_pi(rhs) ? Pi(local, B) : Fun(local, B);
                locals.pop_back();
                expr v         = Fun(locals, binding);
                cs += mk_eq_cnstr(m, v, j);
                alts.push_back(cs.to_list());
            } catch (exception&) {}
            margs.pop_back();
        }

    public:
        flex_rigid_core_fn(unifier_fn & _u, expr const & _lhs, expr const & _rhs,
                           justification const & _j, buffer<constraints> & _alts,
                           bool _imitation_only):
            u(_u), lhs(_lhs), m(get_app_args(lhs, margs)), rhs(_rhs), j(_j), alts(_alts),
            imitation_only(_imitation_only) {}

        void operator()() {
            switch (rhs.kind()) {
            case expr_kind::Var: case expr_kind::Meta:
                lean_unreachable(); // LCOV_EXCL_LINE
            case expr_kind::Local:
                mk_simple_projections();
                break;
            case expr_kind::Sort: case expr_kind::Constant:
                if (!pattern() && !cheap() && !imitation_only)
                    mk_simple_projections();
                mk_simple_imitation();
                break;
            case expr_kind::Pi: case expr_kind::Lambda:
                if (!pattern() && !cheap() && !imitation_only)
                    mk_simple_projections();
                mk_bindings_imitation();
                break;
            case expr_kind::Macro:
                lean_unreachable(); // LCOV_EXCL_LINE
            case expr_kind::App:
                if (!imitation_only)
                    mk_app_projections();
                mk_app_imitation();
                break;
            }
        }
    };

    void process_flex_rigid_core(expr const & lhs, expr const & rhs, justification const & j,
                                 buffer<constraints> & alts, bool imitation_only) {
        flex_rigid_core_fn(*this, lhs, rhs, j, alts, imitation_only)();
    }

    /** \brief When lhs is an application (f ...), make sure that if any argument that is reducible to a
        local constant is replaced with a local constant.

        \remark We store auxiliary constraints created in the reductions in \c aux. We return the new
        "reduce" application.
    */
    expr expose_local_args(expr const & lhs, justification const & j, buffer<constraint> & aux) {
        buffer<expr> margs;
        expr m        = get_app_args(lhs, margs);
        bool modified = false;
        for (expr & marg : margs) {
            // Make sure that if marg is reducible to a local constant, then it is replaced with it.
            if (!is_local(marg)) {
                expr new_marg = whnf(marg, j, aux);
                if (is_local(new_marg)) {
                    marg     = new_marg;
                    modified = true;
                }
            }
        }
        return modified ? mk_app(m, margs) : lhs;
    }

    optional<expr> expand_rhs(expr const & rhs) {
        buffer<expr> args;
        expr const & f = get_app_rev_args(rhs, args);
        lean_assert(!is_local(f) && !is_constant(f) && !is_var(f) && !is_metavar(f));
        if (is_lambda(f)) {
            return some_expr(apply_beta(f, args.size(), args.data()));
        } else if (is_macro(f)) {
            if (optional<expr> new_f = m_tc->expand_macro(f))
                return some_expr(mk_rev_app(*new_f, args.size(), args.data()));
        }
        return none_expr();
    }

    /** \brief When solving flex-rigid constraints lhs =?= rhs (lhs is of the form ?M a_1 ... a_n),
        we consider an additional case-split where rhs is put in weak-head-normal-form when

        1- Option unifier.computation is true
        2- At least one a_i is not a local constant
        3- rhs contains a local constant that is not equal to any a_i.
    */
    bool use_flex_rigid_whnf_split(expr const & lhs, expr const & rhs) {
        lean_assert(is_meta(lhs));
        if (m_config.m_kind != unifier_kind::Liberal)
            return false;
        if (m_config.m_computation)
            return true; // if unifier.computation is true, we always consider the additional whnf split
        // TODO(Leo): perhaps we should use the following heuristic only for coercions
        // automatically generated by structure manager
        if (is_coercion(m_env, get_app_fn(rhs)))
            return false;
        buffer<expr> locals;
        expr const * it = &lhs;
        while (is_app(*it)) {
            expr const & arg = app_arg(*it);
            if (!is_local(arg))
                return true; // lhs contains non-local constant
            locals.push_back(arg);
            it = &(app_fn(*it));
        }
        if (!context_check(rhs, locals))
            return true; // rhs contains local constant that is not in locals
        return false;
    }

    /** \brief Process a flex rigid constraint */
    bool process_flex_rigid(expr lhs, expr const & rhs, justification const & j) {
        lean_assert(is_meta(lhs));
        lean_assert(!is_meta(rhs));
        if (is_app(rhs)) {
            expr const & f = get_app_fn(rhs);
            if (!is_local(f) && !is_constant(f)) {
                if (auto new_rhs = expand_rhs(rhs)) {
                    lean_assert(*new_rhs != rhs);
                    return is_def_eq(lhs, *new_rhs, j);
                } else {
                    return false;
                }
            }
        } else if (is_macro(rhs)) {
            if (auto new_rhs = expand_rhs(rhs)) {
                lean_assert(*new_rhs != rhs);
                return is_def_eq(lhs, *new_rhs, j);
            } else {
                return false;
            }
        }

        buffer<constraint> aux;
        lhs = expose_local_args(lhs, j, aux);
        buffer<constraints> alts;
        process_flex_rigid_core(lhs, rhs, j, alts, false);
        append_auxiliary_constraints(alts, to_list(aux.begin(), aux.end()));
        if (use_flex_rigid_whnf_split(lhs, rhs)) {
            expr rhs_whnf = flex_rigid_whnf(rhs, j, aux);
            if (rhs_whnf != rhs) {
                if (is_meta(rhs_whnf)) {
                    // it become a flex-flex constraint
                    alts.push_back(constraints(mk_eq_cnstr(lhs, rhs_whnf, j)));
                } else {
                    buffer<constraints> alts2;
                    process_flex_rigid_core(lhs, rhs_whnf, j, alts2, true);
                    append_auxiliary_constraints(alts2, to_list(aux.begin(), aux.end()));
                    alts.append(alts2);
                }
            }
        }

        // std::cout << "FlexRigid\n";
        // for (auto cs : alts) {
        //     std::cout << " alternative\n";
        //     for (auto c : cs) {
        //         std::cout << "   >> " << c << "\n";
        //     }
        // }

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
        expr lhs   = cnstr_lhs_expr(c);
        expr rhs   = cnstr_rhs_expr(c);
        if (is_meta(lhs))
            return process_flex_rigid(lhs, rhs, c.get_justification());
        else
            return process_flex_rigid(rhs, lhs, c.get_justification());
    }

    void postpone(constraint const & c) {
        m_postponed = cons(c, m_postponed);
    }

    void discard(constraint const & c) {
        if (!m_config.m_discard)
            postpone(c);
    }

    // Auxiliary method used in process_flex_flex_approx
    bool assign_flex_approx(expr const & m, expr const & v, justification const & j, constraint_seq & cs) {
        lean_assert(m_config.m_discard);
        buffer<expr> args;
        expr const & fn = get_app_args(m, args);
        lean_assert(is_metavar(fn));
        expr type = mlocal_type(fn);
        type = ensure_sufficient_args(type, args.size(), cs);
        buffer<expr> locals;
        for (expr const & a : args) {
            expr local = is_local(a) ? a : mk_local_for(type);
            locals.push_back(local);
            type = instantiate(binding_body(type), local);
        }
        return assign(m, fn, locals, v, j);
    }

    bool process_flex_flex_approx(constraint const & c) {
        lean_assert(m_config.m_discard);
        // Try to solve constraint
        // ?M_1 t_1 ... t_n =?= ?M_2 s_1 ... s_m
        // by creating a fresh metavariable ?M using common local constants.
        // If can't build approximate solution, then discard constraint.
        expr const & lhs = cnstr_lhs_expr(c);
        expr const & rhs = cnstr_rhs_expr(c);
        buffer<expr> lhs_args, rhs_args;
        get_app_args(lhs, lhs_args);
        get_app_args(rhs, rhs_args);
        buffer<expr> shared_locals;
        unsigned sz = std::min(lhs_args.size(), rhs_args.size());
        unsigned i  = 0;
        for (; i < sz; i++) {
            if (!is_local(lhs_args[i]) || !is_local(rhs_args[i]) ||
                mlocal_name(lhs_args[i]) != mlocal_name(rhs_args[i]))
                break;
            shared_locals.push_back(lhs_args[i]);
        }
        constraint_seq cs;
        if (optional<expr> lhs_type = infer(lhs, cs)) {
            expr new_type = Pi(shared_locals, *lhs_type);
            if (!has_local(new_type)) {
                expr new_mvar = mk_metavar(m_ngen.next(), new_type);
                expr new_val  = mk_app(new_mvar, shared_locals);
                justification const & j = c.get_justification();
                return
                    assign_flex_approx(lhs, new_val, j, cs) &&
                    assign_flex_approx(rhs, new_val, j, cs) &&
                    process_constraints(cs, c.get_justification());
            }
        }
        // Failed to generate approximate solution.
        // TODO(Leo): generate an error, or just ingore?
        // we are currently just ignoring...
        return true;
    }


    bool process_flex_flex(constraint const & c) {
        expr const & lhs = cnstr_lhs_expr(c);
        expr const & rhs = cnstr_rhs_expr(c);
        // We ignore almost all flex-flex constraints.
        // We just handle flex_flex "first-order" case
        //   ?M_1 l_1 ... l_k =?= ?M_2 l_1 ... l_k
        //   ?M_1 l_1 ... l_k =?= ?M_2 l_1 ... l_k ... l_n
        //   ?M_1 l_1 ... l_k ... l_n =?= ?M_2 l_1 ... l_k
        if (!is_simple_meta(lhs) || !is_simple_meta(rhs)) {
            if (m_config.m_discard) {
                return process_flex_flex_approx(c);
            } else {
                discard(c);
                return true;
            }
        }
        buffer<expr> lhs_args, rhs_args;
        expr ml = get_app_args(lhs, lhs_args);
        expr mr = get_app_args(rhs, rhs_args);
        if (mlocal_name(ml) == mlocal_name(mr)) {
            discard(c);
            return true;
        }
        unsigned min_sz = std::min(lhs_args.size(), rhs_args.size());
        lean_assert(!m_subst.is_assigned(ml));
        lean_assert(!m_subst.is_assigned(mr));
        unsigned i = 0;
        for (; i < min_sz; i++)
            if (mlocal_name(lhs_args[i]) != mlocal_name(rhs_args[i]))
                break;
        if (i == min_sz) {
            if (lhs_args.size() >= rhs_args.size()) {
                return assign(lhs, ml, lhs_args, rhs, c.get_justification());
            } else {
                return assign(rhs, mr, rhs_args, lhs, c.get_justification());
            }
        } else {
            discard(c);
            return true;
        }
    }

    /** \brief Return true iff \c rhs is of the form <tt> max(l_1 ... lhs ... l_k) </tt>,
        such that l_i's do not contain lhs.

        If the result is true, then all l_i's are stored in rest.
    */
    static bool generalized_check_meta(level const & m, level const & rhs, bool & found_m, buffer<level> & rest) {
        lean_assert(is_meta(m));
        if (is_max(rhs)) {
            return
                generalized_check_meta(m, max_lhs(rhs), found_m, rest) &&
                generalized_check_meta(m, max_rhs(rhs), found_m, rest);
        } else if (m == rhs) {
            found_m = true;
            return true;
        } else if (occurs_meta(m, rhs)) {
            return false;
        } else {
            rest.push_back(rhs);
            return true;
        }
    }

    status process_l_eq_max_core(level const & lhs, level const & rhs, justification const & jst) {
        lean_assert(is_meta(lhs));
        buffer<level> rest;
        bool found_lhs = false;
        if (generalized_check_meta(lhs, rhs, found_lhs, rest)) {
            level r;
            if (found_lhs) {
                // rhs is of the form max(rest, lhs)
                // Solution is lhs := max(rest, ?u) where ?u is fresh metavariable
                r = mk_meta_univ(m_ngen.next());
                rest.push_back(r);
                unsigned i = rest.size();
                while (i > 0) {
                    --i;
                    r = mk_max(rest[i], r);
                }
                r = normalize(r);
            } else {
                // lhs does not occur in rhs
                r = rhs;
            }

            if (assign(lhs, r, jst)) {
                return Solved;
            } else {
                set_conflict(jst);
                return Failed;
            }
        } else {
            return Continue;
        }
    }

    /** \brief Return solved iff \c c is a constraint of the form
                   lhs =?= max(rest, lhs)
               and is successfully solved.
    */
    status process_l_eq_max(constraint const & c) {
        lean_assert(is_level_eq_cnstr(c));
        level lhs = cnstr_lhs_level(c);
        level rhs = cnstr_rhs_level(c);
        justification jst = c.get_justification();
        if (is_meta(lhs))
            return process_l_eq_max_core(lhs, rhs, jst);
        else if (is_meta(rhs))
            return process_l_eq_max_core(rhs, lhs, jst);
        else
            return Continue;
    }

    /** Auxiliary method for process_succ_eq_max */
    status process_succ_eq_max_core(level const & lhs, level const & rhs, justification const & jst) {
        if (!is_succ(lhs) || !is_max(rhs))
            return Continue;
        level m = rhs;
        while (is_max(m)) {
            level m1 = max_lhs(m);
            level m2 = max_rhs(m);
            if (is_geq(lhs, m1)) {
                m = m2;
            } else if (is_geq(lhs, m2)) {
                m = m1;
            } else {
                return Continue;
            }
        }
        if (!is_meta(m))
            return Continue;
        if (assign(m, lhs, jst)) {
            return Solved;
        } else {
            set_conflict(jst);
            return Failed;
        }
    }

    /** \brief Return Solved iff \c c is a constraint of the form
                  succ^k_1 a =?= max(succ^k_2 b, ?m)
               where k_1 >= k_2 and a == b or b == zero

              and is successfully solved by assigning ?m := succ^k_1 a
    */
    status process_succ_eq_max(constraint const & c) {
        lean_assert(is_level_eq_cnstr(c));
        level lhs = cnstr_lhs_level(c);
        level rhs = cnstr_rhs_level(c);
        justification jst = c.get_justification();
        status st = process_succ_eq_max_core(lhs, rhs, jst);
        if (st != Continue) return st;
        return process_succ_eq_max_core(rhs, lhs, jst);
    }

    /**
       \brief Process the following constraints
          1. (max l1 l2) =?= 0    OR
                 solution:  l1 =?= 0, l2 =?= 0
          2. (imax l1 l2) =?= 0
                 solution:  l2 =?= 0
    */
    status try_level_eq_zero(level const & lhs, level const & rhs, justification const & j) {
        if (!is_zero(rhs))
            return Continue;
        if (is_max(lhs)) {
            if (process_constraint(mk_level_eq_cnstr(max_lhs(lhs), rhs, j)) &&
                process_constraint(mk_level_eq_cnstr(max_rhs(lhs), rhs, j)))
                return Solved;
            else
                return Failed;
        } else if (is_imax(lhs)) {
            return process_constraint(mk_level_eq_cnstr(imax_rhs(lhs), rhs, j)) ? Solved : Failed;
        } else {
            return Continue;
        }
    }

    status try_level_eq_zero(constraint const & c) {
        lean_assert(is_level_eq_cnstr(c));
        level const & lhs = cnstr_lhs_level(c);
        level const & rhs = cnstr_rhs_level(c);
        justification const & j = c.get_justification();
        status st = try_level_eq_zero(lhs, rhs, j);
        if (st != Continue) return st;
        return try_level_eq_zero(rhs, lhs, j);
    }

    /** \brief Try to solve constraints of the form
              (?m1 =?= max ?m2 ?m3)
              (?m1 =?= max ?m2 ?m3)
        by assigning ?m1 =?= ?m2 and ?m1 =?= ?m3

        \remark we may miss solutions.
    */
    status try_merge_max_core(level const & lhs, level const & rhs, justification const & j) {
        level m1 = lhs;
        level m2, m3;
        if (is_max(rhs)) {
            m2 = max_lhs(rhs);
            m3 = max_rhs(rhs);
        } else if (is_imax(rhs)) {
            m2 = imax_lhs(rhs);
            m3 = imax_rhs(rhs);
        } else {
            return Continue;
        }
        if (process_constraint(mk_level_eq_cnstr(m1, m2, j)) &&
            process_constraint(mk_level_eq_cnstr(m1, m3, j)))
            return Solved;
        else
            return Failed;
    }

    /** \see try_merge_max_core */
    status try_merge_max(constraint const & c) {
        lean_assert(is_level_eq_cnstr(c));
        level const & lhs = cnstr_lhs_level(c);
        level const & rhs = cnstr_rhs_level(c);
        justification const & j = c.get_justification();
        status st = try_merge_max_core(lhs, rhs, j);
        if (st != Continue) return st;
        return try_merge_max_core(rhs, lhs, j);
    }

    /** \brief Process the next constraint in the constraint queue m_cnstrs */
    bool process_next() {
        lean_assert(!m_cnstrs.empty());
        auto const * p = m_cnstrs.min();
        constraint c   = p->first;
        unsigned cidx  = p->second;
        if (cidx >= get_group_first_index(cnstr_group::ClassInstance) &&
            is_choice_cnstr(c) && cnstr_on_demand(c)) {
            // we postpone class-instance constraints whose type still contains metavariables
            m_cnstrs.erase_min();
            postpone(c);
            return true;
        }
        // std::cout << "process_next: " << c << "\n";
        m_cnstrs.erase_min();
        if (is_choice_cnstr(c)) {
            return process_choice_constraint(c);
        } else {
            auto r = instantiate_metavars(c);
            c = r.first;
            bool modified = r.second;
            if (is_level_eq_cnstr(c)) {
                if (modified) {
                    return process_constraint(c);
                }
                status st = process_l_eq_max(c);
                if (st != Continue) return st == Solved;
                st = process_succ_eq_max(c);
                if (st != Continue) return st == Solved;
                if (m_config.m_discard) {
                    // we only try try_level_eq_zero and try_merge_max when we are discarding
                    // constraints that canno be solved.
                    st = try_level_eq_zero(c);
                    if (st != Continue) return st == Solved;
                    if (cidx < get_group_first_index(cnstr_group::FlexFlex)) {
                        add_cnstr(c, cnstr_group::FlexFlex);
                        return true;
                    }
                    st = try_merge_max(c);
                    if (st != Continue) return st == Solved;
                    return process_plugin_constraint(c);
                } else {
                    discard(c);
                    return true;
                }
            } else {
                lean_assert(is_eq_cnstr(c));
                if (is_delta_cnstr(c)) {
                    return process_delta(c);
                } else if (modified) {
                    return is_def_eq(cnstr_lhs_expr(c), cnstr_rhs_expr(c), c.get_justification());
                } else if (auto d = is_owned(c)) {
                    // Metavariable in the constraint is owned by choice constraint.
                    // choice constraint was postponed... since c was not modifed
                    // So, we should postpone this one too.
                    add_cnstr(c, to_cnstr_group(*d+1));
                    return true;
                } else if (is_flex_rigid(c)) {
                    return process_flex_rigid(c);
                } else if (is_flex_flex(c)) {
                    return process_flex_flex(c);
                } else if (is_same_projection_projection(c)) {
                    return process_same_projection_projection(c);
                } else if (is_projection_projection(c)) {
                    return process_projection_projection(c, cidx);
                } else if (is_projection_lhs(c)) {
                    return process_projection_eq(cnstr_lhs_expr(c), cnstr_rhs_expr(c), c.get_justification());
                } else if (is_projection_rhs(c)) {
                    return process_projection_eq(cnstr_rhs_expr(c), cnstr_lhs_expr(c), c.get_justification());
                } else {
                    return process_plugin_constraint(c);
                }
            }
        }
    }

    /** \brief Return true if unifier may be able to produce more solutions */
    bool more_solutions() const {
        return !in_conflict() || !m_case_splits.empty();
    }

    typedef optional<pair<substitution, constraints>> next_result;

    next_result failure() {
        lean_assert(in_conflict());
        if (m_config.m_use_exceptions)
            throw unifier_exception(*m_conflict, m_subst);
        else
            return next_result();
    }

    /** \brief Produce the next solution */
    next_result next() {
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
            return next_result();
        }

        while (true) {
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
        substitution s = m_subst;
        s.forget_justifications();
        return next_result(mk_pair(s, m_postponed));
    }
};

unify_result_seq unify(std::shared_ptr<unifier_fn> u) {
    if (!u->more_solutions()) {
        u->failure(); // make sure exception is thrown if u->m_use_exception is true
        return unify_result_seq();
    } else {
        return mk_lazy_list<pair<substitution, constraints>>([=]() {
                auto s = u->next();
                if (s)
                    return some(mk_pair(*s, unify(u)));
                else
                    return unify_result_seq::maybe_pair();
            });
    }
}

unify_result_seq unify(environment const & env,  unsigned num_cs, constraint const * cs, name_generator && ngen,
                       substitution const & s, unifier_config const & cfg) {
    return unify(std::make_shared<unifier_fn>(env, num_cs, cs, std::move(ngen), s, cfg));
}

unify_result_seq unify(environment const & env, expr const & lhs, expr const & rhs, name_generator && ngen,
                       substitution const & s, unifier_config const & cfg) {
    substitution new_s = s;
    expr _lhs = new_s.instantiate(lhs);
    expr _rhs = new_s.instantiate(rhs);
    auto u = std::make_shared<unifier_fn>(env, 0, nullptr, std::move(ngen), new_s, cfg);
    constraint_seq cs;
    if (!u->m_tc->is_def_eq(_lhs, _rhs, justification(), cs) || !u->process_constraints(cs)) {
        return unify_result_seq();
    } else {
        return unify(u);
    }
}

static int unify_simple(lua_State * L) {
    int nargs = lua_gettop(L);
    unify_status r;
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
    return push_integer(L, static_cast<unsigned>(r));
}

DECL_UDATA(unify_result_seq)

static const struct luaL_Reg unify_result_seq_m[] = {
    {"__gc", unify_result_seq_gc},
    {0, 0}
};

static int unify_result_seq_next(lua_State * L) {
    unify_result_seq seq = to_unify_result_seq(L, lua_upvalueindex(1));
    unify_result_seq::maybe_pair p;
    p = seq.pull();
    if (p) {
        push_unify_result_seq(L, p->second);
        lua_replace(L, lua_upvalueindex(1));
        push_substitution(L, p->first.first);
        // TODO(Leo): return postponed constraints
    } else {
        lua_pushnil(L);
    }
    return 1;
}

static int push_unify_result_seq_it(lua_State * L, unify_result_seq const & seq) {
    push_unify_result_seq(L, seq);
    lua_pushcclosure(L, &safe_function<unify_result_seq_next>, 1); // create closure with 1 upvalue
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
    return unifier_plugin([=](constraint const & c, name_generator && ngen) {
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

static name * g_tmp_prefix = nullptr;

static int unify(lua_State * L) {
    int nargs = lua_gettop(L);
    unify_result_seq r;
    environment const & env = to_environment(L, 1);
    if (is_expr(L, 2)) {
        if (nargs == 6)
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4).mk_child(), to_substitution(L, 5),
                      unifier_config(to_options(L, 6)));
        else if (nargs == 5)
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4).mk_child(), to_substitution(L, 5));
        else
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4).mk_child());
    } else {
        buffer<constraint> cs;
        to_constraint_buffer(L, 2, cs);
        if (nargs == 5)
            r = unify(env, cs.size(), cs.data(), to_name_generator(L, 3).mk_child(), to_substitution(L, 4),
                      unifier_config(to_options(L, 5)));
        else if (nargs == 4)
            r = unify(env, cs.size(), cs.data(), to_name_generator(L, 3).mk_child(), to_substitution(L, 4));
        else
            r = unify(env, cs.size(), cs.data(), to_name_generator(L, 3).mk_child());
    }
    return push_unify_result_seq_it(L, r);
}

void open_unifier(lua_State * L) {
    luaL_newmetatable(L, unify_result_seq_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, unify_result_seq_m, 0);
    SET_GLOBAL_FUN(unify_result_seq_pred, "is_unify_result_seq");

    SET_GLOBAL_FUN(unify_simple,  "unify_simple");
    SET_GLOBAL_FUN(unify,         "unify");

    lua_newtable(L);
    SET_ENUM("Solved",       unify_status::Solved);
    SET_ENUM("Failed",       unify_status::Failed);
    SET_ENUM("Unsupported",  unify_status::Unsupported);
    lua_setglobal(L, "unify_status");
}

void initialize_unifier() {
    g_unifier_max_steps            = new name{"unifier", "max_steps"};
    g_unifier_normalizer_max_steps = new name{"unifier", "normalizer_max_steps"};
    g_unifier_computation          = new name{"unifier", "computation"};
    g_unifier_expensive_classes    = new name{"unifier", "expensive_classes"};
    g_unifier_conservative         = new name{"unifier", "conservative"};
    g_unifier_nonchronological     = new name{"unifier", "nonchronological"};

    register_unsigned_option(*g_unifier_max_steps, LEAN_DEFAULT_UNIFIER_MAX_STEPS, "(unifier) maximum number of steps");
    register_unsigned_option(*g_unifier_normalizer_max_steps, LEAN_DEFAULT_UNIFIER_NORMALIZER_MAX_STEPS, "(unifier) maximum number of steps the normalization procedure may perform when invoked by the unifier");
    register_bool_option(*g_unifier_computation, LEAN_DEFAULT_UNIFIER_COMPUTATION,
                         "(unifier) always case-split on reduction/computational steps when solving flex-rigid and delta-delta constraints");
    register_bool_option(*g_unifier_expensive_classes, LEAN_DEFAULT_UNIFIER_EXPENSIVE_CLASSES,
                         "(unifier) use \"full\" higher-order unification when solving class instances");
    register_bool_option(*g_unifier_conservative, LEAN_DEFAULT_UNIFIER_CONSERVATIVE,
                         "(unifier) unfolds only constants marked as reducible, avoid expensive case-splits (it is faster but less complete)");
    register_bool_option(*g_unifier_nonchronological, LEAN_DEFAULT_UNIFIER_NONCHRONOLOGICAL,
                         "(unifier) enable/disable nonchronological backtracking in the unifier (this option is only available for debugging and benchmarking purposes, and running experiments)");

    g_dont_care_cnstr = new constraint(mk_eq_cnstr(expr(), expr(), justification()));
    g_tmp_prefix      = new name(name::mk_internal_unique_name());
}

void finalize_unifier() {
    delete g_tmp_prefix;
    delete g_dont_care_cnstr;
    delete g_unifier_max_steps;
    delete g_unifier_normalizer_max_steps;
    delete g_unifier_computation;
    delete g_unifier_expensive_classes;
    delete g_unifier_conservative;
    delete g_unifier_nonchronological;
}
}
