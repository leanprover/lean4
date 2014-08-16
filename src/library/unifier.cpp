/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <memory>
#include <vector>
#include <limits>
#include "util/interrupt.h"
#include "util/luaref.h"
#include "util/lazy_list_fn.h"
#include "util/sstream.h"
#include "util/lbool.h"
#include "util/flet.h"
#include "kernel/for_each_fn.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "kernel/error_msgs.h"
#include "library/occurs.h"
#include "library/locals.h"
#include "library/unifier.h"
#include "library/opaque_hints.h"
#include "library/unifier_plugin.h"
#include "library/kernel_bindings.h"

namespace lean {
static name g_unifier_max_steps      {"unifier", "max_steps"};
RegisterUnsignedOption(g_unifier_max_steps, LEAN_DEFAULT_UNIFIER_MAX_STEPS, "(unifier) maximum number of steps");
unsigned get_unifier_max_steps(options const & opts) { return opts.get_unsigned(g_unifier_max_steps, LEAN_DEFAULT_UNIFIER_MAX_STEPS); }
static name g_unifier_expensive      {"unifier", "expensive"};
RegisterBoolOption(g_unifier_expensive, LEAN_DEFAULT_UNIFIER_EXPENSIVE, "(unifier) enable/disable expensive (and more complete) procedure");
bool get_unifier_expensive(options const & opts) { return opts.get_bool(g_unifier_expensive, LEAN_DEFAULT_UNIFIER_EXPENSIVE); }

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
            if (is_local(e) && !contains_local(e, locals)) {
                failed = true;
                return false;
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
            expr v = Fun(args, rhs);
            s.assign(mlocal_name(*m), v, j);
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

static constraint g_dont_care_cnstr = mk_eq_cnstr(expr(), expr(), justification(), false);
static unsigned g_group_size = 1u << 29;
constexpr unsigned g_num_groups = 7;
static unsigned g_cnstr_group_first_index[g_num_groups] = { 0, g_group_size, 2*g_group_size, 3*g_group_size, 4*g_group_size, 5*g_group_size, 6*g_group_size};
static unsigned get_group_first_index(cnstr_group g) {
    return g_cnstr_group_first_index[static_cast<unsigned>(g)];
}
static unsigned get_group_last_index(cnstr_group g) {
    unsigned g_idx = static_cast<unsigned>(g);
    if (g_idx + 1 < g_num_groups) {
        lean_assert(g_cnstr_group_first_index[g_idx+1] != 0);
        return g_cnstr_group_first_index[g_idx+1]-1;
    } else {
        return std::numeric_limits<unsigned>::max();
    }
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
    typedef std::pair<constraint, unsigned> cnstr; // constraint + idx
    struct cnstr_cmp {
        int operator()(cnstr const & c1, cnstr const & c2) const { return c1.second < c2.second ? -1 : (c1.second == c2.second ? 0 : 1); }
    };
    typedef rb_tree<cnstr, cnstr_cmp> cnstr_set;
    typedef rb_tree<unsigned, unsigned_cmp> cnstr_idx_set;
    typedef rb_map<name, cnstr_idx_set, name_quick_cmp> name_to_cnstrs;
    typedef rb_map<name, unsigned, name_quick_cmp> owned_map;
    typedef std::unique_ptr<type_checker> type_checker_ptr;
    environment      m_env;
    name_generator   m_ngen;
    substitution     m_subst;
    owned_map        m_owned_map; // mapping from metavariable name m to delay factor of the choice constraint that owns m
    unifier_plugin   m_plugin;
    type_checker_ptr m_tc[2];
    bool             m_use_exception; //!< True if we should throw an exception when there are no more solutions.
    unsigned         m_max_steps;
    unsigned         m_num_steps;
    bool             m_expensive;
    bool             m_pattern; //!< If true, then only higher-order (pattern) matching is used
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
        owned_map        m_owned_map;
        bool             m_pattern;

        /** \brief Save unifier's state */
        case_split(unifier_fn & u, justification const & j):
            m_assumption_idx(u.m_next_assumption_idx), m_jst(j), m_subst(u.m_subst), m_cnstrs(u.m_cnstrs),
            m_mvar_occs(u.m_mvar_occs), m_owned_map(u.m_owned_map), m_pattern(u.m_pattern) {
            u.m_next_assumption_idx++;
            u.m_tc[0]->push();
            u.m_tc[1]->push();
        }

        /** \brief Restore unifier's state with saved values, and update m_assumption_idx and m_failed_justifications. */
        void restore_state(unifier_fn & u) {
            lean_assert(u.in_conflict());
            u.m_tc[0]->pop();   // restore type checker state
            u.m_tc[1]->pop();   // restore type checker state
            u.m_tc[0]->push();
            u.m_tc[1]->push();
            u.m_subst     = m_subst;
            u.m_cnstrs    = m_cnstrs;
            u.m_mvar_occs = m_mvar_occs;
            u.m_owned_map = m_owned_map;
            u.m_pattern   = m_pattern;
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
               bool use_exception, unsigned max_steps, bool expensive):
        m_env(env), m_ngen(ngen), m_subst(s), m_plugin(get_unifier_plugin(env)),
        m_use_exception(use_exception), m_max_steps(max_steps), m_num_steps(0), m_expensive(expensive), m_pattern(false) {
        m_tc[0] = mk_type_checker_with_hints(env, m_ngen.mk_child(), false);
        m_tc[1] = mk_type_checker_with_hints(env, m_ngen.mk_child(), true);
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
        unsigned cidx;
        if (g == cnstr_group::ClassInstance) {
            // we use a stack discipline for solving class instances
            cidx = get_group_last_index(g) - m_next_cidx;
        } else {
            cidx = m_next_cidx + get_group_first_index(g);
        }
        m_cnstrs.insert(cnstr(c, cidx));
        m_next_cidx++;
        return cidx;
    }

    /** \brief Check if \c t1 and \c t2 are definitionally equal, if they are not, set a conflict with justification \c j

        \remark If relax is true then opaque definitions from the main module are treated as transparent.
    */
    bool is_def_eq(expr const & t1, expr const & t2, justification const & j, bool relax) {
        if (m_tc[relax]->is_def_eq(t1, t2, j)) {
            return true;
        } else {
            // std::cout << "conflict: " << t1 << " =?= " << t2 << "\n";
            set_conflict(j);
            return false;
        }
    }

    /** \brief Put \c e in weak head normal form.

        \remark If relax is true then opaque definitions from the main module are treated as transparent.
        \remark Constraints generated in the process are stored in \c cs. The justification \c j is composed with them.
    */
    expr whnf(expr const & e, justification const & j, bool relax, buffer<constraint> & cs) {
        unsigned cs_sz = cs.size();
        expr r = m_tc[relax]->whnf(e, cs);
        for (unsigned i = cs_sz; i < cs.size(); i++)
            cs[i] = update_justification(cs[i], mk_composite1(j, cs[i].get_justification()));
        return r;
    }

    /** \brief Process the given constraints. Return true iff no conflict was detected. */
    bool process_constraints(buffer<constraint> & cs) {
        for (auto const & c : cs)
            if (!process_constraint(c))
                return false;
        return true;
    }

    /** \brief Infer \c e type.

        \remark Return none if an exception was throw when inferring the type.
        \remark If relax is true then opaque definitions from the main module are treated as transparent.
        \remark Constraints generated in the process are stored in \c cs. The justification \c j is composed with them.
    */
    optional<expr> infer(expr const & e, justification const & j, bool relax, buffer<constraint> & cs) {
        try {
            unsigned cs_sz = cs.size();
            expr r = m_tc[relax]->infer(e, cs);
            for (unsigned i = cs_sz; i < cs.size(); i++)
                cs[i] = update_justification(cs[i], mk_composite1(j, cs[i].get_justification()));
            return some_expr(r);
        } catch (exception &) {
            return none_expr();
        }
    }

    justification mk_assign_justification(expr const & m, expr const & m_type, expr const & v_type, justification const & j) {
        auto r = j.get_main_expr();
        if (!r) r = m;
        justification new_j = mk_justification(r, [=](formatter const & fmt, substitution const & subst) {
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
                r += compose(line(), format("the assignment was attempted when trying to solve"));
                r += nest(2*get_pp_indent(fmt.get_options()), compose(line(), j.pp(fmt, nullptr, subst)));
                return r;
            });
        return mk_composite1(new_j, j);
    }

    /**
       \brief Assign \c v to metavariable \c m with justification \c j.
       The type of v and m are inferred, and is_def_eq is invoked.
       Any constraint that contains \c m is revisited.

       \remark If relax is true then opaque definitions from the main module are treated as transparent.
    */
    bool assign(expr const & m, expr const & v, justification const & j, bool relax,
                expr const & lhs, expr const & rhs) {
        lean_assert(is_metavar(m));
        lean_assert(!in_conflict());
        m_subst.assign(m, v, j);
        #if 0
        expr m_type = mlocal_type(m);
        expr v_type;
        buffer<constraint> cs;
        if (auto type = infer(v, j, relax, cs)) {
            v_type = *type;
            if (!process_constraints(cs))
                return false;
        } else {
            set_conflict(j);
            return false;
        }
        lean_assert(!in_conflict());
        justification new_j = mk_assign_justification(m, m_type, v_type, j);
        if (!is_def_eq(m_type, v_type, new_j, relax))
            return false;
        #else
        buffer<constraint> cs;
        auto lhs_type = infer(lhs, j, relax, cs);
        auto rhs_type = infer(rhs, j, relax, cs);
        if (lhs_type && rhs_type) {
            if (!process_constraints(cs))
                return false;
            justification new_j = mk_assign_justification(m, *lhs_type, *rhs_type, j);
            if (!is_def_eq(*lhs_type, *rhs_type, new_j, relax))
                return false;
        } else {
            set_conflict(j);
            return false;
        }
        #endif
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

    justification mk_invalid_local_ctx_justification(expr const & lhs, expr const & rhs, justification const & j, expr const & bad_local) {
        justification new_j = mk_justification(get_app_fn(lhs), [=](formatter const & fmt, substitution const & subst) {
                format r = format("invalid local context when tried to assign");
                r += pp_indent_expr(fmt, rhs);
                buffer<expr> locals;
                auto m = get_app_args(lhs, locals);
                r += format({line(), format("containing '"), fmt(bad_local), format("', to placeholder '"), fmt(m), format("'")});
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
                r += compose(line(), format("the assignment was attempted when trying to solve"));
                r += nest(2*get_pp_indent(fmt.get_options()), compose(line(), j.pp(fmt, nullptr, subst)));
                return r;
            });
        return mk_composite1(new_j, j);
    }

    enum status { Solved, Failed, Continue };
    /**
       \brief Process constraints of the form <tt>lhs =?= rhs</tt> where lhs is of the form <tt>?m</tt> or <tt>(?m l_1 .... l_n)</tt>,
       where all \c l_i are distinct local variables. In this case, the method returns Solved, if the method assign succeeds.
       The method returns \c Failed if \c rhs contains <tt>?m</tt>, or it contains a local constant not in <tt>{l_1, ..., l_n}</tt>.
       Otherwise, it returns \c Continue.
    */
    status process_metavar_eq(expr const & lhs, expr const & rhs, justification const & j, bool relax) {
        if (!is_meta(lhs))
            return Continue;
        buffer<expr> locals;
        auto m = is_simple_meta(lhs, locals);
        if (!m || is_meta(rhs))
            return Continue;
        expr bad_local;
        switch (occurs_context_check(m_subst, rhs, *m, locals, bad_local)) {
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
            if (assign(*m, Fun(locals, rhs), j, relax, lhs, rhs)) {
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
            auto lhs_jst = m_subst.instantiate_metavars(cnstr_lhs_expr(c));
            auto rhs_jst = m_subst.instantiate_metavars(cnstr_rhs_expr(c));
            expr lhs = lhs_jst.first;
            expr rhs = rhs_jst.first;
            if (lhs != cnstr_lhs_expr(c) || rhs != cnstr_rhs_expr(c)) {
                return mk_pair(mk_eq_cnstr(lhs, rhs,
                                           mk_composite1(mk_composite1(c.get_justification(), lhs_jst.second), rhs_jst.second),
                                           relax_main_opaque(c)),
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
        bool relax = relax_main_opaque(c);

        if (lhs == rhs)
            return Solved; // trivial constraint

        // Update justification using the justification of the instantiated metavariables
        if (!has_metavar(lhs) && !has_metavar(rhs)) {
            return is_def_eq(lhs, rhs, jst, relax) ? Solved : Failed;
        }

        // Handle higher-order pattern matching.
        status st = process_metavar_eq(lhs, rhs, jst, relax);
        if (st != Continue) return st;
        st = process_metavar_eq(rhs, lhs, jst, relax);
        if (st != Continue) return st;

        return Continue;
    }

    expr instantiate_meta(expr e, justification & j) {
        while (true) {
            expr const & f = get_app_fn(e);
            if (!is_metavar(f))
                return e;
            name const & f_name = mlocal_name(f);
            auto f_value = m_subst.get_expr(f_name);
            if (!f_value)
                return e;
            j = mk_composite1(j, m_subst.get_expr_jst(f_name));
            buffer<expr> args;
            get_app_rev_args(e, args);
            e = apply_beta(*f_value, args.size(), args.data());
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
            return is_def_eq(lhs, rhs, j, relax_main_opaque(c)) ? Solved : Failed;
        lhs = instantiate_meta_args(lhs, j);
        rhs = instantiate_meta_args(rhs, j);
        if (lhs != cnstr_lhs_expr(c) || rhs != cnstr_rhs_expr(c))
            return is_def_eq(lhs, rhs, j, relax_main_opaque(c)) ? Solved : Failed;
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
        bool relax = relax_main_opaque(c);

        if (is_eq_deltas(lhs, rhs)) {
            // we need to create a backtracking point for this one
            add_cnstr(c, cnstr_group::Basic);
        } else if (is_meta(lhs) && is_meta(rhs)) {
            // flex-flex constraints are delayed the most.
            unsigned cidx = add_cnstr(c, cnstr_group::FlexFlex);
            add_meta_occ(lhs, cidx);
            add_meta_occ(rhs, cidx);
        } else if (m_plugin->delay_constraint(*m_tc[relax], c)) {
            unsigned cidx = add_cnstr(c, cnstr_group::PluginDelayed);
            add_meta_occs(lhs, cidx);
            add_meta_occs(rhs, cidx);
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

    bool preprocess_choice_constraint(constraint const & c) {
        if (cnstr_is_owner(c)) {
            expr m = get_app_fn(cnstr_expr(c));
            lean_assert(is_metavar(m));
            m_owned_map.insert(mlocal_name(m), cnstr_delay_factor(c));
        }
        // Choice constraints are never considered easy.
        add_cnstr(c, get_choice_cnstr_group(c));
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
        m_tc[0]->pop();
        m_tc[1]->pop();
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
        buffer<constraint> cs;
        bool relax = relax_main_opaque(c);
        lean_assert(!m_tc[relax]->next_cnstr());
        if (!m_tc[relax]->is_def_eq(f_lhs, f_rhs, j, cs))
            return lazy_list<constraints>();
        buffer<expr> args_lhs, args_rhs;
        get_app_args(lhs, args_lhs);
        get_app_args(rhs, args_rhs);
        if (args_lhs.size() != args_rhs.size())
            return lazy_list<constraints>();
        lean_assert(!m_tc[relax]->next_cnstr());
        for (unsigned i = 0; i < args_lhs.size(); i++)
            if (!m_tc[relax]->is_def_eq(args_lhs[i], args_rhs[i], j, cs))
                return lazy_list<constraints>();
        return lazy_list<constraints>(to_list(cs.begin(), cs.end()));
    }

    bool process_plugin_constraint(constraint const & c) {
        bool relax = relax_main_opaque(c);
        lean_assert(!is_choice_cnstr(c));
        lean_assert(!m_tc[relax]->next_cnstr());
        lazy_list<constraints> alts = m_plugin->solve(*m_tc[relax], c, m_ngen.mk_child());
        lean_assert(!m_tc[relax]->next_cnstr());
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
        bool relax = relax_main_opaque(c);

        buffer<constraint> cs;
        if (auto type = infer(m, c.get_justification(), relax, cs)) {
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

        justification a;
        // add case_split for t =?= s
        expr lhs_fn_val = instantiate_value_univ_params(d, const_levels(lhs_fn));
        expr rhs_fn_val = instantiate_value_univ_params(d, const_levels(rhs_fn));
        expr t = apply_beta(lhs_fn_val, lhs_args.size(), lhs_args.data());
        expr s = apply_beta(rhs_fn_val, rhs_args.size(), rhs_args.data());
        bool relax = relax_main_opaque(c);
        buffer<constraint> cs2;
        if (m_tc[relax]->is_def_eq(t, s, j, cs2)) {
            // create a case split
            a = mk_assumption_justification(m_next_assumption_idx);
            add_case_split(std::unique_ptr<case_split>(new simple_case_split(*this, j, to_list(cs2.begin(), cs2.end()))));
        }

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
            if (!is_def_eq(lhs_args[i], rhs_args[i], new_j, relax))
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

    /** \brief Append the auxiliary constraints \c aux to each alternative in \c alts */
    void append_auxiliary_constraints(buffer<constraints> & alts, list<constraint> const & aux) {
        if (is_nil(aux))
            return;
        for (constraints & cs : alts)
            cs = append(aux, cs);
    }

    /** \brief Auxiliary functional object for implementing process_flex_rigid_core */
    class flex_rigid_core_fn {
        unifier_fn &          u;
        expr const &          lhs;
        buffer<expr>          margs;
        expr const &          m;
        expr const &          rhs;
        justification         j;
        bool                  relax;
        buffer<constraints> & alts; // result: alternatives

        optional<bool>        _has_meta_args;
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

        /** \brief Copy pending constraints in u.m_tc[relax] to cs and append justification j to them */
        void copy_pending_constraints(buffer<constraint> & cs) {
            while (auto c = u.m_tc[relax]->next_cnstr())
                cs.push_back(update_justification(*c, mk_composite1(c->get_justification(), j)));
        }

        /** \see ensure_sufficient_args */
        expr ensure_sufficient_args_core(expr mtype, unsigned i) {
            if (i == margs.size())
                return mtype;
            mtype = u.m_tc[relax]->ensure_pi(mtype);
            expr local = u.mk_local_for(mtype);
            expr body  = instantiate(binding_body(mtype), local);
            return Pi(local, ensure_sufficient_args_core(body, i+1));
        }

        /** \brief Make sure mtype is a Pi of size at least margs.size().
            If it is not, we use ensure_pi and (potentially) add new constaints to enforce it.
        */
        expr ensure_sufficient_args(expr const & mtype, buffer<constraint> & cs) {
            expr t = mtype;
            unsigned num = 0;
            while (is_pi(t)) {
                num++;
                t = binding_body(t);
            }
            if (num == margs.size())
                return mtype;
            lean_assert(!u.m_tc[relax]->next_cnstr()); // make sure there are no pending constraints
            // We must create a scope to make sure no constraints "leak" into the current state.
            type_checker::scope scope(*u.m_tc[relax]);
            auto new_mtype = ensure_sufficient_args_core(mtype, 0);
            copy_pending_constraints(cs);
            return new_mtype;
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
            buffer<constraint> cs;
            auto new_mtype = ensure_sufficient_args(mtype, cs);
            cs.push_back(mk_eq_cnstr(m, mk_lambda_for(new_mtype, rhs), j, relax));
            alts.push_back(to_list(cs.begin(), cs.end()));
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
            buffer<constraint> cs;
            auto new_mtype = ensure_sufficient_args(mtype, cs);
            // Remark: we should not use mk_eq_cnstr(marg, rhs, j) since is_def_eq may be able to reduce them.
            // The unifier assumes the eq constraints are reduced.
            if (u.m_tc[relax]->is_def_eq_types(marg, rhs, j, cs) &&
                u.m_tc[relax]->is_def_eq(marg, rhs, j, cs)) {
                expr v = mk_lambda_for(new_mtype, mk_var(vidx));
                cs.push_back(mk_eq_cnstr(m, v, j, relax));
                alts.push_back(to_list(cs.begin(), cs.end()));
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
                } else if (is_local(marg) && is_local(rhs) && mlocal_name(marg) == mlocal_name(rhs)) {
                    // if the argument is local, and rhs is equal to it, then we also add a projection
                    buffer<constraint> cs;
                    auto new_mtype = ensure_sufficient_args(mtype, cs);
                    expr v = mk_lambda_for(new_mtype, mk_var(vidx));
                    cs.push_back(mk_eq_cnstr(m, v, j, relax));
                    alts.push_back(to_list(cs.begin(), cs.end()));
                }
            }
        }

        /**
           \see mk_flex_rigid_app_cnstrs
           When using "imitation" for solving a constraint
                ?m l_1 ... l_k =?= f a_1 ... a_n
           We say argument a_i is "easy" if
                 1) it is a local constant
                 2) there is only one l_j equal to a_i.
                 3) none of the l_j's is of the form (?m ...)
           In our experiments, the vast majority (> 2/3 of all cases) of the arguments are easy.

           margs contains l_1 ... l_k
           arg is the argument we are testing

           Result: none if it is not an easy argument, and variable #k-i-1 if it is easy.
           The variable is the "solution".
        */
        optional<expr> is_easy_flex_rigid_arg(expr const & arg) {
            if (!is_local(arg))
                return none_expr();
            optional<expr> v;
            unsigned num_margs = margs.size();
            for (unsigned j = 0; j < num_margs; j++) {
                if (is_meta(margs[j]))
                    return none_expr();
                if (is_local(margs[j]) && mlocal_name(arg) == mlocal_name(margs[j])) {
                    if (v)
                        return none_expr(); // failed, there is more than one possibility
                    v = mk_var(num_margs - j - 1);
                }
            }
            return v;
        }

        /** \brief Check if term \c e (produced by an imitation step) is
            type correct, and store generated constraints in \c cs.
            Include \c j in all generated constraints */
        bool check_imitation(expr e, buffer<constraint> & cs) {
            buffer<expr> ls;
            while (is_lambda(e)) {
                expr d = instantiate_rev(binding_domain(e), ls.size(), ls.data());
                expr l = mk_local(u.m_ngen.next(), binding_name(e), d, binding_info(e));
                ls.push_back(l);
                e = binding_body(e);
            }
            e = instantiate_rev(e, ls.size(), ls.data());;
            try {
                buffer<constraint> aux;
                u.m_tc[relax]->check(e, aux);
                for (auto c : aux) {
                    cs.push_back(update_justification(c, mk_composite1(j, c.get_justification())));
                }
                return true;
            } catch (exception&) {
                return false;
            }
        }

        void mk_app_projections() {
            lean_assert(is_metavar(m));
            lean_assert(is_app(rhs));
            if (!u.m_pattern) {
                expr const & f = get_app_fn(rhs);
                lean_assert(is_constant(f) || is_local(f));
                if (is_local(f)) {
                    unsigned i = margs.size();
                    if (!u.m_pattern) {
                        while (i > 0) {
                            --i;
                            if (!(is_local(margs[i]) && mlocal_name(margs[i]) == mlocal_name(f)))
                                mk_simple_nonlocal_projection(i);
                        }
                    }
                } else {
                    mk_simple_projections();
                }
            }
        }

        /** \brief Create the local context \c locals for the imitiation step.
         */
        void mk_local_context(buffer<expr> & locals, buffer<constraint> & cs) {
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

        expr mk_imitiation_arg(expr const & arg, expr const & type, buffer<expr> const & locals,
                               buffer<constraint> & cs) {
            if (!has_meta_args() && is_local(arg) && contains_local(arg, locals)) {
                return arg;
            } else {
                // std::cout << "type: " << type << "\n";
                if (context_check(type, locals)) {
                    expr maux    = mk_metavar(u.m_ngen.next(), Pi(locals, type));
                    // std::cout << "  >> " << maux << " : " << mlocal_type(maux) << "\n";
                    cs.push_back(mk_eq_cnstr(mk_app(maux, margs), arg, j, relax));
                    return mk_app(maux, locals);
                } else {
                    expr maux_type   = mk_metavar(u.m_ngen.next(), Pi(locals, mk_sort(mk_meta_univ(u.m_ngen.next()))));
                    expr maux        = mk_metavar(u.m_ngen.next(), Pi(locals, mk_app(maux_type, locals)));
                    cs.push_back(mk_eq_cnstr(mk_app(maux, margs), arg, j, relax));
                    return mk_app(maux, locals);
                }
            }
        }

        void mk_app_imitation_core(expr const & f, buffer<expr> const & locals, buffer<constraint> & cs) {
            buffer<expr> rargs;
            get_app_args(rhs, rargs);
            buffer<expr> sargs;
            try {
                // create a scope to make sure no constraints "leak" into the current state
                type_checker::scope scope(*u.m_tc[relax]);
                expr f_type = u.m_tc[relax]->infer(f);
                for (expr const & rarg : rargs) {
                    f_type      = u.m_tc[relax]->ensure_pi(f_type);
                    expr d_type = binding_domain(f_type);
                    expr sarg   = mk_imitiation_arg(rarg, d_type, locals, cs);
                    sargs.push_back(sarg);
                    f_type      = instantiate(binding_body(f_type), sarg);
                }
                copy_pending_constraints(cs);
            } catch (exception&) {}
            expr v = Fun(locals, mk_app(f, sargs));
            // std::cout << " >> app imitation, v: " << v << "\n";
            lean_assert(!has_local(v));
            cs.push_back(mk_eq_cnstr(m, v, j, relax));
            alts.push_back(to_list(cs.begin(), cs.end()));
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

           If f is a constant, then g is f.
           If f is a local constant, then we consider each a_i that is equal to f.

           Remark: we try to minimize the number of constraints (?m_i a_1 ... a_k) =?= b_i by detecting "easy" cases
           that can be solved immediately. See \c mk_imitiation_arg
        */
        void mk_app_imitation() {
            lean_assert(is_metavar(m));
            lean_assert(is_app(rhs));
            lean_assert(!u.m_tc[relax]->next_cnstr()); // make sure there are no pending constraints
            buffer<expr> locals;
            buffer<constraint> cs;
            flet<justification> let(j, j); // save j value
            mk_local_context(locals, cs);
            lean_assert(margs.size() == locals.size());
            expr const & f = get_app_fn(rhs);
            lean_assert(is_constant(f) || is_local(f));
            if (is_local(f)) {
                unsigned cs_sz = cs.size();
                unsigned i = margs.size();
                while (i > 0) {
                    --i;
                    if (is_local(margs[i]) && mlocal_name(margs[i]) == mlocal_name(f)) {
                        cs.shrink(cs_sz);
                        mk_app_imitation_core(locals[i], locals, cs);
                    }
                }
            } else {
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
            lean_assert(!u.m_tc[relax]->next_cnstr()); // make sure there are no pending constraints
            buffer<constraint> cs;
            buffer<expr> locals;
            flet<justification> let(j, j); // save j value
            mk_local_context(locals, cs);
            lean_assert(margs.size() == locals.size());
            try {
                // create a scope to make sure no constraints "leak" into the current state
                type_checker::scope scope(*u.m_tc[relax]);
                expr rhs_A     = binding_domain(rhs);
                expr A_type    = u.m_tc[relax]->infer(rhs_A);
                expr A         = mk_imitiation_arg(rhs_A, A_type, locals, cs);
                expr local     = mk_local(u.m_ngen.next(), binding_name(rhs), A, binding_info(rhs));
                locals.push_back(local);
                margs.push_back(local);
                expr rhs_B     = instantiate(binding_body(rhs), local);
                expr B_type    = u.m_tc[relax]->infer(rhs_B);
                expr B         = mk_imitiation_arg(rhs_B, B_type, locals, cs);
                expr binding   = is_pi(rhs) ? Pi(local, B) : Fun(local, B);
                locals.pop_back();
                expr v         = Fun(locals, binding);
                copy_pending_constraints(cs);
                cs.push_back(mk_eq_cnstr(m, v, j, relax));
                alts.push_back(to_list(cs.begin(), cs.end()));
            } catch (exception&) {}
            margs.pop_back();
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
        void mk_macro_imitation() {
            lean_assert(is_metavar(m));
            lean_assert(is_macro(rhs));
            buffer<constraint> cs;
            expr mtype = mlocal_type(m);
            mtype = ensure_sufficient_args(mtype, cs);
            // create an auxiliary metavariable for each macro argument
            buffer<expr> sargs;
            for (unsigned i = 0; i < macro_num_args(rhs); i++) {
                expr maux = mk_aux_metavar_for(u.m_ngen, mtype);
                cs.push_back(mk_eq_cnstr(mk_app(maux, margs), macro_arg(rhs, i), j, relax));
                sargs.push_back(mk_app_vars(maux, margs.size()));
            }
            expr v = mk_macro(macro_def(rhs), sargs.size(), sargs.data());
            v = mk_lambda_for(mtype, v);
            if (check_imitation(v, cs)) {
                cs.push_back(mk_eq_cnstr(m, v, j, relax));
                alts.push_back(to_list(cs.begin(), cs.end()));
            }
        }

    public:
        flex_rigid_core_fn(unifier_fn & _u, expr const & _lhs, expr const & _rhs,
                           justification const & _j, bool _relax, buffer<constraints> & _alts):
            u(_u), lhs(_lhs), m(get_app_args(lhs, margs)), rhs(_rhs), j(_j), relax(_relax), alts(_alts) {}

        void operator()() {
            switch (rhs.kind()) {
            case expr_kind::Var: case expr_kind::Meta:
                lean_unreachable(); // LCOV_EXCL_LINE
            case expr_kind::Local:
                mk_simple_projections();
                break;
            case expr_kind::Sort: case expr_kind::Constant:
                if (!u.m_pattern)
                    mk_simple_projections();
                mk_simple_imitation();
                break;
            case expr_kind::Pi: case expr_kind::Lambda:
                if (!u.m_pattern)
                    mk_simple_projections();
                mk_bindings_imitation();
                break;
            case expr_kind::Macro:
                if (!u.m_pattern)
                    mk_simple_projections();
                mk_macro_imitation();
                break;
            case expr_kind::App:
                mk_app_projections();
                mk_app_imitation();
                break;
            }
        }
    };

    void process_flex_rigid_core(expr const & lhs, expr const & rhs, justification const & j, bool relax,
                                 buffer<constraints> & alts) {
        flex_rigid_core_fn(*this, lhs, rhs, j, relax, alts)();
    }

    /** \brief When lhs is an application (f ...), make sure that if any argument that is reducible to a
        local constant is replaced with a local constant.

        \remark We store auxiliary constraints created in the reductions in \c aux. We return the new
        "reduce" application.

        \remark We need this step because of the optimization based on is_easy_flex_rigid_arg
    */
    expr expose_local_args(expr const & lhs, justification const & j, bool relax, buffer<constraint> & aux) {
        buffer<expr> margs;
        expr m        = get_app_args(lhs, margs);
        bool modified = false;
        for (expr & marg : margs) {
            // Make sure that if marg is reducible to a local constant, then it is replaced with it.
            // We need that because of the optimization based on is_easy_flex_rigid_arg
            if (!is_local(marg)) {
                expr new_marg = whnf(marg, j, relax, aux);
                if (is_local(new_marg)) {
                    marg     = new_marg;
                    modified = true;
                }
            }
        }
        return modified ? mk_app(m, margs) : lhs;
    }

    /** \brief Process a flex rigid constraint */
    bool process_flex_rigid(expr lhs, expr const & rhs, justification const & j, bool relax) {
        lean_assert(is_meta(lhs));
        lean_assert(!is_meta(rhs));
        if (is_app(rhs)) {
            expr const & f = get_app_fn(rhs);
            if (!is_local(f) && !is_constant(f)) {
                buffer<constraint> cs;
                expr new_rhs = whnf(rhs, j, relax, cs);
                lean_assert(new_rhs != rhs);
                if (!process_constraints(cs))
                    return false;
                return is_def_eq(lhs, new_rhs, j, relax);
            }
        }

        buffer<constraint> aux;
        lhs = expose_local_args(lhs, j, relax, aux);
        buffer<constraints> alts;
        process_flex_rigid_core(lhs, rhs, j, relax, alts);
        append_auxiliary_constraints(alts, to_list(aux.begin(), aux.end()));
        if (m_expensive) {
            expr rhs_whnf = whnf(rhs, j, relax, aux);
            if (rhs_whnf != rhs) {
                buffer<constraints> alts2;
                process_flex_rigid_core(lhs, rhs_whnf, j, relax, alts2);
                append_auxiliary_constraints(alts2, to_list(aux.begin(), aux.end()));
                alts.append(alts2);
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
        bool relax = relax_main_opaque(c);
        if (is_meta(lhs))
            return process_flex_rigid(lhs, rhs, c.get_justification(), relax);
        else
            return process_flex_rigid(rhs, lhs, c.get_justification(), relax);
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
            if (mlocal_name(lhs_args[i]) != mlocal_name(rhs_args[i]))
                break;
        if (i == lhs_args.size())
            return assign(ml, mr, c.get_justification(), relax_main_opaque(c), lhs, rhs);
        return true;
    }

    void consume_tc_cnstrs() {
        while (true) {
            if (in_conflict()) {
                return;
            } else if (auto c = m_tc[0]->next_cnstr()) {
                process_constraint(*c);
            } else if (auto c = m_tc[1]->next_cnstr()) {
                process_constraint(*c);
            } else {
                break;
            }
        }
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
        lean_assert(!m_tc[0]->next_cnstr());
        lean_assert(!m_tc[1]->next_cnstr());
        auto const * p = m_cnstrs.min();
        unsigned cidx  = p->second;
        if (!m_expensive && cidx >= get_group_first_index(cnstr_group::ClassInstance))
            m_pattern = true; // use only higher-order (pattern) matching after we start processing class-instance constraints
        constraint c   = p->first;
        // std::cout << "process_next: " << c << "\n";
        m_cnstrs.erase_min();
        if (is_choice_cnstr(c)) {
            return process_choice_constraint(c);
        } else {
            auto r = instantiate_metavars(c);
            c = r.first;
            lean_assert(!m_tc[0]->next_cnstr());
            lean_assert(!m_tc[1]->next_cnstr());
            bool modified = r.second;
            if (is_level_eq_cnstr(c)) {
                if (modified)
                    return process_constraint(c);
                status st = try_level_eq_zero(c);
                if (st != Continue) return st == Solved;
                if (cidx < get_group_first_index(cnstr_group::FlexFlex)) {
                    add_cnstr(c, cnstr_group::FlexFlex);
                    return true;
                }
                st = try_merge_max(c);
                if (st != Continue) return st == Solved;
                return process_plugin_constraint(c);
            } else {
                lean_assert(is_eq_cnstr(c));
                if (is_delta_cnstr(c)) {
                    return process_delta(c);
                } else if (modified) {
                    return is_def_eq(cnstr_lhs_expr(c), cnstr_rhs_expr(c), c.get_justification(), relax_main_opaque(c));
                } else if (is_flex_rigid(c)) {
                    return process_flex_rigid(c);
                } else if (is_flex_flex(c)) {
                    return process_flex_flex(c);
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
        lean_assert(!m_tc[0]->next_cnstr());
        lean_assert(!m_tc[1]->next_cnstr());
        lean_assert(!in_conflict());
        lean_assert(m_cnstrs.empty());
        substitution s = m_subst;
        s.forget_justifications();
        return optional<substitution>(s);
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
                              bool use_exception, unsigned max_steps, bool expensive) {
    return unify(std::make_shared<unifier_fn>(env, num_cs, cs, ngen, substitution(), use_exception, max_steps, expensive));
}

lazy_list<substitution> unify(environment const & env,  unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              bool use_exception, options const & o) {
    return unify(env, num_cs, cs, ngen, use_exception, get_unifier_max_steps(o), get_unifier_expensive(o));
}

lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen,
                              bool relax, substitution const & s, unsigned max_steps, bool expensive) {
    substitution new_s = s;
    expr _lhs = new_s.instantiate(lhs);
    expr _rhs = new_s.instantiate(rhs);
    auto u = std::make_shared<unifier_fn>(env, 0, nullptr, ngen, new_s, false, max_steps, expensive);
    if (!u->m_tc[relax]->is_def_eq(_lhs, _rhs))
        return lazy_list<substitution>();
    else
        return unify(u);
}

lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen,
                              bool relax, substitution const & s, options const & o) {
    return unify(env, lhs, rhs, ngen, relax, s, get_unifier_max_steps(o), get_unifier_expensive(o));
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
        if (nargs == 7)
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4), lua_toboolean(L, 5), to_substitution(L, 6), to_options(L, 7));
        else if (nargs == 6)
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4), lua_toboolean(L, 5), to_substitution(L, 6), options());
        else
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4), lua_toboolean(L, 5));
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
