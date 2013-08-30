/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <deque>
#include "elaborator.h"
#include "metavar.h"
#include "printer.h"
#include "context.h"
#include "builtin.h"
#include "free_vars.h"
#include "for_each.h"
#include "replace.h"
#include "flet.h"
#include "elaborator_exception.h"

namespace lean {
static name g_overload_name(name(name(name(0u), "library"), "overload"));
static expr g_overload = mk_constant(g_overload_name);

bool is_overload_marker(expr const & e) {
    return e == g_overload;
}

expr mk_overload_marker() {
    return g_overload;
}

class elaborator::imp {
    // unification constraint lhs == second
    struct constraint {
        expr     m_lhs;
        expr     m_rhs;
        context  m_ctx;
        expr     m_source;     // auxiliary field used for producing error msgs
        context  m_source_ctx; // auxiliary field used for producing error msgs
        unsigned m_arg_pos;    // auxiliary field used for producing error msgs
        constraint(expr const & lhs, expr const & rhs, context const & ctx, expr const & src, context const & src_ctx, unsigned arg_pos):
            m_lhs(lhs), m_rhs(rhs), m_ctx(ctx), m_source(src), m_source_ctx(src_ctx), m_arg_pos(arg_pos) {}
        constraint(expr const & lhs, expr const & rhs, constraint const & c):
            m_lhs(lhs), m_rhs(rhs), m_ctx(c.m_ctx), m_source(c.m_source), m_source_ctx(c.m_source_ctx), m_arg_pos(c.m_arg_pos) {}
        constraint(expr const & lhs, expr const & rhs, context const & ctx, constraint const & c):
            m_lhs(lhs), m_rhs(rhs), m_ctx(ctx), m_source(c.m_source), m_source_ctx(c.m_source_ctx), m_arg_pos(c.m_arg_pos) {}
    };

    // information associated with the metavariable
    struct metavar_info {
        expr    m_assignment;
        expr    m_type;
        expr    m_mvar;
        context m_ctx;
        bool    m_mark; // for implementing occurs check
        metavar_info() {
            m_mark = false;
        }
    };

    typedef std::deque<constraint>    constraint_queue;
    typedef std::vector<metavar_info> metavars;

    environment const & m_env;
    name_set const *    m_available_defs;
    elaborator const *  m_owner;

    constraint_queue    m_constraints;
    metavars            m_metavars;

    bool                m_add_constraints;

    volatile bool       m_interrupted;

    expr metavar_type(expr const & m) {
        lean_assert(is_metavar(m));
        unsigned midx = metavar_idx(m);
        if (m_metavars[midx].m_type) {
            return m_metavars[midx].m_type;
        } else {
            expr t = mk_metavar();
            m_metavars[midx].m_type = t;
            return t;
        }
    }

    expr lookup(context const & c, unsigned i) {
        auto p = lookup_ext(c, i);
        context_entry const & def = p.first;
        context const & def_c     = p.second;
        lean_assert(length(c) > length(def_c));
        return lift_free_vars_mmv(def.get_domain(), 0, length(c) - length(def_c));
    }

    expr check_pi(expr const & e, context const & ctx, expr const & s, context const & s_ctx) {
        check_interrupted(m_interrupted);
        if (is_pi(e)) {
            return e;
        } else {
            expr r = head_reduce_mmv(e, m_env, m_available_defs);
            if (!is_eqp(r, e)) {
                return check_pi(r, ctx, s, s_ctx);
            } else if (is_var(e)) {
                try {
                    auto p = lookup_ext(ctx, var_idx(e));
                    context_entry const & entry = p.first;
                    context const & entry_ctx   = p.second;
                    if (entry.get_body()) {
                        return lift_free_vars_mmv(check_pi(entry.get_body(), entry_ctx, s, s_ctx), 0, length(ctx) - length(entry_ctx));
                    }
                } catch (exception&) {
                    // this can happen if we access a variable out of scope
                    throw function_expected_exception(m_env, s_ctx, s);
                }
            }
            throw function_expected_exception(m_env, s_ctx, s);
        }
    }

    level check_universe(expr const & e, context const & ctx, expr const & s, context const & s_ctx) {
        check_interrupted(m_interrupted);
        if (is_metavar(e)) {
            // approx: assume it is level 0
            return level();
        } else if (is_type(e)) {
            return ty_level(e);
        } else {
            expr r = head_reduce_mmv(e, m_env, m_available_defs);
            if (!is_eqp(r, e)) {
                return check_universe(r, ctx, s, s_ctx);
            } else if (is_var(e)) {
                try {
                    auto p = lookup_ext(ctx, var_idx(e));
                    context_entry const & entry = p.first;
                    context const & entry_ctx   = p.second;
                    if (entry.get_body()) {
                        return check_universe(entry.get_body(), entry_ctx, s, s_ctx);
                    }
                } catch (exception&) {
                    // this can happen if we access a variable out of scope
                    throw type_expected_exception(m_env, s_ctx, s);
                }
            }
            throw type_expected_exception(m_env, s_ctx, s);
        }
    }

    void add_constraint(expr const & t1, expr const & t2, context const & ctx, expr const & s, unsigned arg_pos) {
        if (has_metavar(t1) || has_metavar(t2)) {
            m_constraints.push_back(constraint(t1, t2, ctx, s, ctx, arg_pos));
        }
    }

    expr infer(expr const & e, context const & ctx) {
        check_interrupted(m_interrupted);
        switch (e.kind()) {
        case expr_kind::Constant:
            if (is_metavar(e)) {
                unsigned midx = metavar_idx(e);
                if (!(m_metavars[midx].m_ctx)) {
                    lean_assert(!(m_metavars[midx].m_mvar));
                    m_metavars[midx].m_mvar = e;
                    m_metavars[midx].m_ctx  = ctx;
                }
                return metavar_type(e);
            } else {
                return m_env.get_object(const_name(e)).get_type();
            }
        case expr_kind::Var:
            return lookup(ctx, var_idx(e));
        case expr_kind::Type:
            return mk_type(ty_level(e) + 1);
        case expr_kind::Value:
            return to_value(e).get_type();
        case expr_kind::App: {
            buffer<expr> types;
            unsigned num = num_args(e);
            for (unsigned i = 0; i < num; i++) {
                types.push_back(infer(arg(e,i), ctx));
            }
            // TODO: handle overload in args[0]
            expr f_t = types[0];
            if (!f_t) {
                throw invalid_placeholder_exception(*m_owner, ctx, e);
            }
            for (unsigned i = 1; i < num; i++) {
                f_t = check_pi(f_t, ctx, e, ctx);
                if (m_add_constraints)
                    add_constraint(abst_domain(f_t), types[i], ctx, e, i);
                f_t = instantiate_free_var_mmv(abst_body(f_t), 0, arg(e, i));
            }
            return f_t;
        }
        case expr_kind::Eq: {
            infer(eq_lhs(e), ctx);
            infer(eq_rhs(e), ctx);
            return mk_bool_type();
        }
        case expr_kind::Pi: {
            expr dt = infer(abst_domain(e), ctx);
            expr bt = infer(abst_body(e), extend(ctx, abst_name(e), abst_domain(e)));
            return mk_type(max(check_universe(dt, ctx, e, ctx), check_universe(bt, ctx, e, ctx)));
        }
        case expr_kind::Lambda: {
            expr dt = infer(abst_domain(e), ctx);
            expr bt = infer(abst_body(e), extend(ctx, abst_name(e), abst_domain(e)));
            return mk_pi(abst_name(e), abst_domain(e), bt);
        }
        case expr_kind::Let: {
            expr lt = infer(let_value(e), ctx);
            return infer(let_body(e), extend(ctx, let_name(e), lt, let_value(e)));
        }}
        lean_unreachable();
        return expr();
    }

    bool is_simple_ho_match(expr const & e1, expr const & e2, context const & ctx) {
        if (is_app(e1) && is_meta(arg(e1,0)) && is_var(arg(e1,1), 0) && num_args(e1) == 2 && length(ctx) > 0) {
            return true;
        } else {
            return false;
        }
    }

    void unify_simple_ho_match(expr const & e1, expr const & e2, constraint const & c) {
        context const & ctx = c.m_ctx;
        m_constraints.push_back(constraint(arg(e1,0), mk_lambda(car(ctx).get_name(), car(ctx).get_domain(), e2), c));
    }

    struct cycle_detected {};
    void occ_core(expr const & t) {
        check_interrupted(m_interrupted);
        auto proc = [&](expr const & e, unsigned offset) {
            if (is_metavar(e)) {
                unsigned midx = metavar_idx(e);
                if (m_metavars[midx].m_mark)
                    throw cycle_detected();
                if (m_metavars[midx].m_assignment) {
                    flet<bool> set(m_metavars[midx].m_mark, true);
                    occ_core(m_metavars[midx].m_assignment);
                }
            }
        };
        for_each_fn<decltype(proc)> visitor(proc);
        visitor(t);
    }

    // occurs check
    bool occ(expr const & t, unsigned midx) {
        lean_assert(!m_metavars[midx].m_mark);
        flet<bool> set(m_metavars[midx].m_mark, true);
        try {
            occ_core(t);
            return true;
        } catch (cycle_detected&) {
            return false;
        }
    }

    [[noreturn]] void throw_unification_exception(constraint const & c) {
        // display(std::cout);
        m_constraints.push_back(c);
        if (c.m_arg_pos != static_cast<unsigned>(-1)) {
            throw unification_app_mismatch_exception(*m_owner, c.m_source_ctx, c.m_source, c.m_arg_pos);
        } else {
            throw unification_type_mismatch_exception(*m_owner, c.m_source_ctx, c.m_source);
        }
    }

    void solve_mvar(expr const & m, expr const & t, constraint const & c) {
        lean_assert(is_metavar(m));
        unsigned midx = metavar_idx(m);
        if (m_metavars[midx].m_assignment) {
            m_constraints.push_back(constraint(m_metavars[midx].m_assignment, t, c));
        } else if (has_metavar(t, midx) || !occ(t, midx)) {
            throw_unification_exception(c);
        } else {
            m_metavars[midx].m_assignment = t;
        }
    }

    bool solve_meta(expr const & e, expr const & t, constraint const & c) {
        lean_assert(!is_metavar(e));
        expr const & m = get_metavar(e);
        unsigned midx  = metavar_idx(m);
        unsigned i, s, n;
        expr v, a, b;

        if (m_metavars[midx].m_assignment) {
            expr s = instantiate_metavar(e, midx, m_metavars[midx].m_assignment);
            m_constraints.push_back(constraint(s, t, c));
            return true;
        }

        if (!has_metavar(t)) {
            if (is_lower(e, a, s, n)) {
                m_constraints.push_back(constraint(a, lift_free_vars_mmv(t, s-n, n), c));
                return true;
            }

            if (is_lift(e, a, s, n)) {
                if (!has_free_var(t, s, s+n)) {
                    m_constraints.push_back(constraint(a, lower_free_vars_mmv(t, s+n, n), c));
                    return true;
                } else {
                    // display(std::cout);
                    throw_unification_exception(c);
                }
            }
        }

        if (has_assigned_metavar(t)) {
            m_constraints.push_back(constraint(e, instantiate(t), c));
            return true;
        }

        if (is_subst(e, a, i, v) && is_lift(a, b, s, n) && has_free_var(t, s, s+n)) {
            // subst (lift b s n) i v  ==  t
            // (lift b s n) does not have free-variables in the range [s, s+n)
            // Thus, if t has a free variables in [s, s+n), then the only possible solution is
            //    (lift b s n) == i
            //    v == t
            m_constraints.push_back(constraint(a, mk_var(i), c));
            m_constraints.push_back(constraint(v, t, c));
            return true;
        }

        return false;
    }

    void solve_core() {
        unsigned delayed = 0;
        unsigned last_num_constraints = 0;
        while (!m_constraints.empty()) {
            check_interrupted(m_interrupted);
            constraint c = m_constraints.front();
            m_constraints.pop_front();
            expr const & lhs = c.m_lhs;
            expr const & rhs = c.m_rhs;
            // std::cout << "Solving " << lhs << " === " << rhs << "\n";
            if (lhs == rhs || (!has_metavar(lhs) && !has_metavar(rhs))) {
                // do nothing
                delayed = 0;
            } else if (is_metavar(lhs)) {
                delayed = 0;
                solve_mvar(lhs, rhs, c);
            } else if (is_metavar(rhs)) {
                delayed = 0;
                solve_mvar(rhs, lhs, c);
            } else if (is_meta(lhs) || is_meta(rhs)) {
                if (is_meta(lhs) && solve_meta(lhs, rhs, c)) {
                    delayed = 0;
                } else if (is_meta(rhs) && solve_meta(rhs, lhs, c)) {
                    delayed = 0;
                } else {
                    m_constraints.push_back(c);
                    if (delayed == 0) {
                        last_num_constraints = m_constraints.size();
                        delayed++;
                    } else if (delayed > last_num_constraints) {
                        throw_unification_exception(c);
                    } else {
                        delayed++;
                    }
                }
            } else if (is_type(lhs) && is_type(rhs)) {
                delayed = 0;
                return; // ignoring type universe levels. We let the kernel check that
            } else if (is_abstraction(lhs) && is_abstraction(rhs)) {
                delayed = 0;
                m_constraints.push_back(constraint(abst_domain(lhs), abst_domain(rhs), c));
                m_constraints.push_back(constraint(abst_body(lhs),   abst_body(rhs), extend(c.m_ctx, abst_name(lhs), abst_domain(lhs)), c));
            } else if (is_eq(lhs) && is_eq(rhs)) {
                delayed = 0;
                m_constraints.push_back(constraint(eq_lhs(lhs), eq_lhs(rhs), c));
                m_constraints.push_back(constraint(eq_rhs(lhs), eq_rhs(rhs), c));
            } else {
                expr new_lhs = head_reduce_mmv(lhs, m_env, m_available_defs);
                expr new_rhs = head_reduce_mmv(rhs, m_env, m_available_defs);
                if (!is_eqp(lhs, new_lhs) || !is_eqp(rhs, new_rhs)) {
                    delayed = 0;
                    m_constraints.push_back(constraint(new_lhs, new_rhs, c));
                } else if (is_app(new_lhs) && is_app(new_rhs) && num_args(new_lhs) == num_args(new_rhs)) {
                    delayed = 0;
                    unsigned num = num_args(new_lhs);
                    for (unsigned i = 0; i < num; i++) {
                        m_constraints.push_back(constraint(arg(new_lhs, i), arg(new_rhs, i), c));
                    }
                } else if (is_simple_ho_match(new_lhs, new_rhs, c.m_ctx)) {
                    delayed = 0;
                    unify_simple_ho_match(new_lhs, new_rhs, c);
                } else if (is_simple_ho_match(new_rhs, new_lhs, c.m_ctx)) {
                    delayed = 0;
                    unify_simple_ho_match(new_rhs, new_lhs, c);
                } else {
                    throw_unification_exception(c);
                }
            }
        }
    }

    struct found_assigned {};
    bool has_assigned_metavar(expr const & e) {
        auto proc = [&](expr const & n, unsigned offset) {
            if (is_metavar(n)) {
                unsigned midx = metavar_idx(n);
                if (m_metavars[midx].m_assignment)
                    throw found_assigned();
            }
        };
        for_each_fn<decltype(proc)> visitor(proc);
        try {
            visitor(e);
            return false;
        } catch (found_assigned&) {
            return true;
        }
    }

    expr instantiate(expr const & e) {
        auto proc = [&](expr const & n, unsigned offset) {
            if (is_meta(n)) {
                expr const & m = get_metavar(n);
                unsigned midx = metavar_idx(m);
                if (m_metavars[midx].m_assignment) {
                    if (has_assigned_metavar(m_metavars[midx].m_assignment)) {
                        m_metavars[midx].m_assignment = instantiate(m_metavars[midx].m_assignment);
                    }
                    return instantiate_metavar(n, midx, m_metavars[midx].m_assignment);
                }
            }
            return n;
        };
        replace_fn<decltype(proc)> replacer(proc);
        return replacer(e);
    }

    void solve(unsigned num_meta) {
        m_add_constraints = false;
        while (true) {
            solve_core();
            bool cont     = false;
            bool progress = false;
            unsigned unsolved_midx = 0;
            for (unsigned midx = 0; midx < num_meta; midx++) {
                if (m_metavars[midx].m_assignment) {
                    if (has_assigned_metavar(m_metavars[midx].m_assignment)) {
                        m_metavars[midx].m_assignment = instantiate(m_metavars[midx].m_assignment);
                    }
                    if (has_metavar(m_metavars[midx].m_assignment)) {
                        unsolved_midx = midx;
                        cont = true; // must continue
                    } else {
                        if (m_metavars[midx].m_type) {
                            try {
                                expr t = infer(m_metavars[midx].m_assignment, m_metavars[midx].m_ctx);
                                m_constraints.push_back(constraint(m_metavars[midx].m_type, t, m_metavars[midx].m_ctx,
                                                                   m_metavars[midx].m_mvar, m_metavars[midx].m_ctx, static_cast<unsigned>(-1)));
                                progress = true;
                            } catch (exception&) {
                                // std::cout << "Failed to infer: " << m_metavars[midx].m_assignment << "\nAT\n" << m_metavars[midx].m_ctx << "\n";
                                throw unification_type_mismatch_exception(*m_owner, m_metavars[midx].m_ctx, m_metavars[midx].m_mvar);
                            }
                        }
                    }
                }
            }
            if (!cont)
                return;
            if (!progress)
                throw unsolved_placeholder_exception(*m_owner, m_metavars[unsolved_midx].m_ctx, m_metavars[unsolved_midx].m_mvar);
        }
    }


public:
    imp(environment const & env, name_set const * defs):
        m_env(env),
        m_available_defs(defs) {
        m_interrupted = false;
        m_owner = nullptr;
    }

    expr mk_metavar() {
        unsigned midx = m_metavars.size();
        expr r = ::lean::mk_metavar(midx);
        m_metavars.push_back(metavar_info());
        return r;
    }

    void clear() {
        m_constraints.clear();
        m_metavars.clear();
    }

    void set_interrupt(bool flag) {
        m_interrupted = flag;
    }

    void display(std::ostream & out) {
        for (unsigned i = 0; i < m_metavars.size(); i++) {
            out << "#" << i << " ";
            auto m = m_metavars[i];
            if (m.m_assignment)
                out << m.m_assignment;
            else
                out << "[unassigned]";
            if (m.m_type)
                out << ", type: " << m.m_type;
            out << "\n";
        }

        for (auto c : m_constraints) {
            out << c.m_lhs << " === " << c.m_rhs << "\n";
        }
    }

    environment const & get_environment() const {
        return m_env;
    }

    expr operator()(expr const & e, elaborator const & elb) {
        m_owner = &elb;
        unsigned num_meta = m_metavars.size();
        m_add_constraints = true;
        infer(e, context());
        solve(num_meta);
        return instantiate(e);
    }
};
elaborator::elaborator(environment const & env):m_ptr(new imp(env, nullptr)) {}
elaborator::~elaborator() {}
expr elaborator::mk_metavar() { return m_ptr->mk_metavar(); }
expr elaborator::operator()(expr const & e) { return (*m_ptr)(e, *this); }
void elaborator::set_interrupt(bool flag) { m_ptr->set_interrupt(flag); }
void elaborator::clear() { m_ptr->clear(); }
environment const & elaborator::get_environment() const { return m_ptr->get_environment(); }
void elaborator::display(std::ostream & out) const { m_ptr->display(out); }
}
