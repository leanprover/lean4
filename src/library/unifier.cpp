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
#include "kernel/for_each_fn.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "library/unifier.h"
#include "library/kernel_bindings.h"

namespace lean {
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

// Return true if \c e does not contain the metavariable \c m, and all local
// constants are in \c e are in \c locals
bool occurs_context_check(expr const & e, expr const & m, buffer<expr> const & locals) {
    bool failed = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (failed)
                return false;
            if (is_local(e) && std::find(locals.begin(), locals.end(), e) == locals.end()) {
                // right-hand-side contains variable that is not in the scope
                // of metavariable.
                failed = true;
                return false;
            }
            if (is_metavar(e) && e == m) {
                // occurs-check failed
                failed = true;
                return false;
            }
            // we only need to continue exploring e if it contains
            // metavariables and/or local constants.
            return has_metavar(e) || has_local(e);
        });
    return !failed;
}

// Create a lambda abstraction by abstracting the local constants \c locals in \c e
expr lambda_abstract_locals(expr const & e, buffer<expr> const & locals) {
    expr v = abstract_locals(e, locals.size(), locals.data());
    unsigned i = locals.size();
    while (i > 0) {
        --i;
        v = mk_lambda(local_pp_name(locals[i]), mlocal_type(locals[i]), v);
    }
    return v;
}

static std::pair<unify_status, substitution> unify_simple_core(substitution const & s, expr const & lhs, expr const & rhs,
                                                               justification const & j) {
    lean_assert(is_meta(lhs));
    buffer<expr> args;
    auto m = is_simple_meta(lhs, args);
    if (!m || (is_meta(rhs) && get_app_fn(rhs) == *m)) {
        return mk_pair(unify_status::Unsupported, s);
    } else if (!occurs_context_check(rhs, *m, args)) {
        return mk_pair(unify_status::Failed, s);
    } else {
        expr v = lambda_abstract_locals(rhs, args);
        return mk_pair(unify_status::Solved, s.assign(mlocal_name(*m), v, j));
    }
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
bool occurs(level const & m, level const & e) {
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
    bool contains = occurs(lhs, rhs);
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

struct unifier_fn {
    typedef std::pair<constraint, unsigned> cnstr; // constraint + idx
    struct cnstr_cmp {
        int operator()(cnstr const & c1, cnstr const & c2) const { return c1.second < c2.second ? -1 : (c1.second == c2.second ? 0 : 1); }
    };
    struct unsigned_cmp {
        int operator()(unsigned i1, unsigned i2) const { return i1 < i2 ? -1 : (i1 == i2 ? 0 : 1); }
    };
    typedef rb_tree<cnstr, cnstr_cmp> cnstr_set;
    typedef rb_tree<unsigned, unsigned_cmp> cnstr_idx_set;
    typedef rb_map<name, cnstr_idx_set, name_quick_cmp> name_to_cnstrs;

    environment      m_env;
    name_generator   m_ngen;
    substitution     m_subst;
    unifier_plugin   m_plugin;
    type_checker     m_tc;
    bool             m_use_exception;
    bool             m_first;
    unsigned         m_next_assumption_idx;
    unsigned         m_next_cidx;
    cnstr_set        m_active;
    cnstr_set        m_delayed;
    name_to_cnstrs   m_mvar_occs;
    name_to_cnstrs   m_mlvl_occs;

    struct case_split {
        unsigned         m_assumption_idx; // idx of the current assumption
        justification    m_failed_justifications; // justifications for failed branches
        // snapshot of unifier's state
        substitution     m_subst;
        cnstr_set        m_active;
        cnstr_set        m_delayed;
        name_to_cnstrs   m_mvar_occs;
        name_to_cnstrs   m_mlvl_occs;

        // Save unifier's state
        case_split(unifier_fn & u):
            m_assumption_idx(u.m_next_assumption_idx), m_subst(u.m_subst), m_active(u.m_active), m_delayed(u.m_delayed),
            m_mvar_occs(u.m_mvar_occs), m_mlvl_occs(u.m_mlvl_occs) {
            u.m_next_assumption_idx++;
            u.m_tc.push();
        }

        // Restore unifier's state with saved values, and update m_assumption_idx and m_failed_justifications
        void restore_state(unifier_fn & u) {
            lean_assert(u.in_conflict());
            u.m_tc.pop();   // restore type checker state
            u.m_tc.push();
            u.m_subst     = m_subst;
            u.m_active    = m_active;
            u.m_delayed   = m_delayed;
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
        expr                        m_mvar;
        justification               m_jst;
        lazy_list<choice_fn_result> m_tail;
        choice_case_split(unifier_fn & u, expr const & mvar, justification const & j, lazy_list<choice_fn_result> const & tail):
            case_split(u), m_mvar(mvar), m_jst(j), m_tail(tail) {}
        virtual bool next(unifier_fn & u) { return u.next_choice_case_split(*this); }
    };

    case_split_stack        m_case_splits;
    optional<justification> m_conflict;

    unifier_fn(environment const & env, unsigned num_cs, constraint const * cs,
               name_generator const & ngen, substitution const & s, unifier_plugin const & p,
               bool use_exception):
        m_env(env), m_ngen(ngen), m_subst(s), m_plugin(p),
        m_tc(env, m_ngen.mk_child(), [=](constraint const & c) { process_constraint(c); }),
        m_use_exception(use_exception) {
        m_next_assumption_idx = 0;
        m_next_cidx = 0;
        m_first     = true;
        for (unsigned i = 0; i < num_cs; i++) {
            process_constraint(cs[i]);
        }
    }

    void check_system() {
        check_interrupted();
        // TODO(Leo): check if exceeded the maximum number of steps
    }

    bool in_conflict() const { return (bool)m_conflict; } // NOLINT
    void set_conflict(justification const & j) { m_conflict = j; }
    void update_conflict(justification const & j) { m_conflict = j; }
    void reset_conflict() { m_conflict = optional<justification>(); lean_assert(!in_conflict()); }

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

    void add_mvar_occ(name const & m, unsigned cidx) { add_occ<true>(m, cidx); }
    void add_mlvl_occ(name const & m, unsigned cidx) { add_occ<false>(m, cidx); }

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

    void add_active(constraint const & c, name_set const * mlvl_occs, name_set const * mvar_occs) {
        m_active.insert(cnstr(c, m_next_cidx));
        add_occs(m_next_cidx, mlvl_occs, mvar_occs);
        m_next_cidx++;
    }

    void add_delayed(constraint const & c, name_set const * mlvl_occs, name_set const * mvar_occs) {
        m_delayed.insert(cnstr(c, m_next_cidx));
        add_occs(m_next_cidx, mlvl_occs, mvar_occs);
        m_next_cidx++;
    }

    bool assign(expr const & m, expr const & v, justification const & j) {
        lean_assert(is_metavar(m));
        m_subst = m_subst.assign(m, v, j);
        expr m_type = mlocal_type(m);
        expr v_type = m_tc.infer(v);
        if (in_conflict() || !m_tc.is_def_eq(m_type, v_type, j))
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
    status process_metavar_eq(expr const & lhs, expr const & rhs, justification const & j) {
        if (!is_meta(lhs))
            return Continue;
        buffer<expr> locals;
        auto m = is_simple_meta(lhs, locals);
        if (!m || (is_meta(rhs) && get_app_fn(rhs) == *m))
            return Continue;
        if (!occurs_context_check(rhs, *m, locals)) {
            set_conflict(j);
            return Failed;
        }
        lean_assert(!m_subst.is_assigned(*m));
        if (assign(*m, lambda_abstract_locals(rhs, locals), j)) {
            return Assigned;
        } else {
            return Failed;
        }
    }

    bool process_eq_constraint(constraint const & c) {
        lean_assert(is_eq_cnstr(c));
        // instantiate
        name_set unassigned_lvls, unassigned_exprs;
        auto lhs_jst = m_subst.instantiate_metavars(cnstr_lhs_expr(c), &unassigned_lvls, &unassigned_exprs);
        auto rhs_jst = m_subst.instantiate_metavars(cnstr_rhs_expr(c), &unassigned_lvls, &unassigned_exprs);
        expr const & lhs = lhs_jst.first;
        expr const & rhs = rhs_jst.first;

        if (lhs == rhs)
            return true; // trivial constraint

        justification new_jst = mk_composite1(mk_composite1(c.get_justification(), lhs_jst.second), rhs_jst.second);
        if (!has_metavar(lhs) && !has_metavar(rhs)) {
            set_conflict(new_jst);
            return false; // trivial failure
        }

        status st = process_metavar_eq(lhs, rhs, new_jst);
        if (st != Continue) return st == Assigned;
        st = process_metavar_eq(rhs, lhs, new_jst);
        if (st != Continue) return st == Assigned;

        if (lhs != cnstr_lhs_expr(c) || rhs != cnstr_rhs_expr(c)) {
            // some metavariables were instantiated, try is_def_eq again
            if (m_tc.is_def_eq(lhs, rhs, new_jst)) {
                return true;
            } else {
                set_conflict(new_jst);
                return false;
            }
        }

        if (is_meta(lhs) || is_meta(rhs)) {
            add_delayed(c, &unassigned_lvls, &unassigned_exprs);
        } else {
            add_active(c, &unassigned_lvls, &unassigned_exprs);
        }
        return true;
    }

    status process_metavar_eq(level const & lhs, level const & rhs, justification const & j) {
        if (!is_meta(lhs))
            return Continue;
        bool contains = occurs(lhs, rhs);
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

    bool process_level_eq_constraint(constraint const & c) {
        lean_assert(is_level_eq_cnstr(c));
        name_set unassigned_lvls;
        auto lhs_jst = m_subst.instantiate_metavars(cnstr_lhs_level(c), &unassigned_lvls);
        auto rhs_jst = m_subst.instantiate_metavars(cnstr_rhs_level(c), &unassigned_lvls);
        level lhs = lhs_jst.first;
        level rhs = rhs_jst.first;

        lhs = normalize(lhs);
        rhs = normalize(rhs);
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
            add_delayed(new_c, &unassigned_lvls, nullptr);
        } else {
            add_delayed(c, &unassigned_lvls, nullptr);
        }

        return true;
    }

    bool process_constraint(constraint const & c) {
        if (in_conflict())
            return false;
        check_system();
        switch (c.kind()) {
        case constraint_kind::Choice:
            add_active(c, nullptr, nullptr);
            return true;
        case constraint_kind::Eq:
            return process_eq_constraint(c);
        case constraint_kind::LevelEq:
            return process_level_eq_constraint(c);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    bool process_constraint_cidx(unsigned cidx) {
        if (in_conflict())
            return false;
        cnstr c(g_dont_care_cnstr, cidx);
        if (auto it = m_active.find(c)) {
            lean_assert(!m_delayed.contains(c));
            constraint c2 = it->first;
            m_active.erase(c);
            return process_constraint(c2);
        }
        if (auto it = m_delayed.find(c)) {
            constraint c2 = it->first;
            m_delayed.erase(c);
            return process_constraint(c2);
        }
        return true;
    }

    void add_case_split(std::unique_ptr<case_split> && cs) {
        m_case_splits.push_back(std::move(cs));
    }

    bool resolve_conflict() {
        lean_assert(in_conflict());
        while (!m_case_splits.empty()) {
            std::unique_ptr<case_split> & d = m_case_splits.back();
            if (depends_on(*m_conflict, d->m_assumption_idx)) {
                d->m_failed_justifications = mk_composite1(d->m_failed_justifications, *m_conflict);
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
        // TODO(Leo): if m_use_exception == true, then throw exception instead of returning none.
        return optional<substitution>();
    }

    // Process constraints in \c cs, and append justification \c j to them.
    bool process_constraints(constraints const & cs, justification const & j) {
        for (constraint const & c : cs)
            process_constraint(update_justification(c, mk_composite1(c.get_justification(), j)));
        return !in_conflict();
    }

    bool process_choice_result(expr const & m, choice_fn_result const & r, justification j) {
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
            return process_choice_result(cs.m_mvar, r->first, mk_composite1(cs.m_jst, a));
        } else {
            // update conflict
            update_conflict(mk_composite1(*m_conflict, cs.m_failed_justifications));
            return false;
        }
    }

    bool process_choice_constraint(constraint const & c) {
        lean_assert(is_choice_cnstr(c));
        expr const &   m     = cnstr_mvar(c);
        choice_fn const & fn = cnstr_choice_fn(c);
        lean_assert(is_meta(m));
        auto m_type_jst      = m_subst.instantiate_metavars(m_tc.infer(m), nullptr, nullptr);
        auto rlist           = fn(m_type_jst.first, m_subst, m_ngen.mk_child());
        auto r               = rlist.pull();
        justification j      = mk_composite1(c.get_justification(), m_type_jst.second);
        if (r) {
            justification a = mk_assumption_justification(m_next_assumption_idx);
            add_case_split(std::unique_ptr<case_split>(new choice_case_split(*this, m, m_type_jst.second, r->second)));
            return process_choice_result(m, r->first, mk_composite1(j, a));
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

    bool process_next_active() {
        lean_assert(!m_active.empty());
        constraint c = m_active.min()->first;
        m_active.erase_min();
        if (is_choice_cnstr(c))
            return process_choice_constraint(c);
        else
            return process_plugin_constraint(c);
    }

    bool process_next_delayed() {
        // TODO(Leo)
        return true;
    }

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
        while (!m_active.empty() || !m_delayed.empty()) {
            check_system();
            lean_assert(!in_conflict());
            bool ok = true;
            if (!m_active.empty())
                ok = process_next_active();
            else
                ok = process_next_delayed();
            if (!ok && !resolve_conflict())
                return failure();
        }
        lean_assert(!in_conflict())
        lean_assert(m_active.empty() && m_delayed.empty());
        return optional<substitution>(m_subst);
    }
};

lazy_list<substitution> unify(std::shared_ptr<unifier_fn> const & u) {
    return mk_lazy_list<substitution>([=]() {
            auto s = u->next();
            if (s)
                return some(mk_pair(*s, unify(u)));
            else
                return lazy_list<substitution>::maybe_pair();
        });
}

lazy_list<substitution> unify(environment const & env,  unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              unifier_plugin const & p, bool use_exception) {
    return unify(std::make_shared<unifier_fn>(env, num_cs, cs, ngen, substitution(), p, use_exception));
}

lazy_list<substitution> unify(environment const & env, unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              bool use_exception) {
    return unify(env, num_cs, cs, ngen, [](constraint const &, name_generator const &) { return lazy_list<constraints>(); }, use_exception);
}

lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen, unifier_plugin const & p) {
    substitution s;
    buffer<constraint> cs;
    name_generator new_ngen(ngen);
    bool failed = false;
    type_checker tc(env, new_ngen.mk_child(), [&](constraint const & c) {
            if (!failed) {
                auto r = unify_simple(s, c);
                switch (r.first) {
                case unify_status::Solved:
                    s = r.second; break;
                case unify_status::Failed:
                    failed = true; break;
                case unify_status::Unsupported:
                    cs.push_back(c); break;
                }
            }
        });
    if (!tc.is_def_eq(lhs, rhs) || failed) {
        return lazy_list<substitution>();
    } else if (cs.empty()) {
        return lazy_list<substitution>(s);
    } else {
        return unify(std::make_shared<unifier_fn>(env, cs.size(), cs.data(), ngen, s, p, false));
    }
}

lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen) {
    return unify(env, lhs, rhs, ngen, [](constraint const &, name_generator const &) { return lazy_list<constraints>(); });
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
        else if (nargs == 4 && is_name_generator(L, 4))
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4));
        else if (nargs == 4)
            r = unify(env, to_expr(L, 2), to_expr(L, 3), name_generator(g_tmp_prefix), to_unifier_plugin(L, 4));
        else
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4), to_unifier_plugin(L, 5));
    } else {
        buffer<constraint> cs;
        to_constraint_buffer(L, 2, cs);
        if (nargs == 2)
            r = unify(env, cs.size(), cs.data(), name_generator(g_tmp_prefix));
        else if (nargs == 3 && is_name_generator(L, 3))
            r = unify(env, cs.size(), cs.data(), to_name_generator(L, 3));
        else if (nargs == 3)
            r = unify(env, cs.size(), cs.data(), name_generator(g_tmp_prefix), to_unifier_plugin(L, 3));
        else
            r = unify(env, cs.size(), cs.data(), to_name_generator(L, 3), to_unifier_plugin(L, 4));
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
