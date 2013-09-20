/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <deque>
#include <limits>
#include <utility>
#include <vector>
#include "util/flet.h"
#include "util/name_set.h"
#include "kernel/normalizer.h"
#include "kernel/context.h"
#include "kernel/builtin.h"
#include "kernel/free_vars.h"
#include "kernel/for_each.h"
#include "kernel/replace.h"
#include "kernel/instantiate.h"
#include "kernel/metavar.h"
#include "library/printer.h"
#include "library/placeholder.h"
#include "library/reduce.h"
#include "library/update_expr.h"
#include "library/expr_pair.h"
#include "frontends/lean/frontend.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/elaborator_exception.h"

namespace lean {
static name g_choice_name(name(name(name(0u), "library"), "choice"));
static expr g_choice = mk_constant(g_choice_name);
static format g_assignment_fmt  = format(":=");
static format g_unification_u_fmt = format("\u2248");
static format g_unification_fmt = format("=?=");

expr mk_choice(unsigned num_fs, expr const * fs) {
    lean_assert(num_fs >= 2);
    return mk_eq(g_choice, mk_app(num_fs, fs));
}

bool is_choice(expr const & e) {
    return is_eq(e) && eq_lhs(e) == g_choice;
}

unsigned get_num_choices(expr const & e) {
    lean_assert(is_choice(e));
    return num_args(eq_rhs(e));
}

expr const & get_choice(expr const & e, unsigned i) {
    lean_assert(is_choice(e));
    return arg(eq_rhs(e), i);
}

class elaborator::imp {
    // Information for producing error messages regarding application type mismatch during elaboration
    struct app_mismatch_info {
        expr              m_app;     // original application
        context           m_ctx; // context where application occurs
        std::vector<expr> m_args;    // arguments after processing
        std::vector<expr> m_types;   // inferred types of the arguments
        app_mismatch_info(expr const & app, context const & ctx, unsigned sz, expr const * args, expr const * types):
            m_app(app), m_ctx(ctx), m_args(args, args+sz), m_types(types, types+sz) {}
    };

    // Information for producing error messages regarding expected type mismatch during elaboration
    struct expected_type_info {
        expr              m_expr;  // original expression
        expr              m_processed_expr; // expression after processing
        expr              m_expected;  // expected type
        expr              m_given;  // inferred type of the processed expr.
        context           m_ctx;
        expected_type_info(expr const & e, expr const & p, expr const & exp, expr const & given, context const & ctx):
            m_expr(e), m_processed_expr(p), m_expected(exp), m_given(given), m_ctx(ctx) {}
    };

    enum class info_kind { AppMismatchInfo, ExpectedTypeInfo };

    typedef std::pair<info_kind, unsigned> info_ref;

    std::vector<app_mismatch_info>  m_app_mismatch_info;
    std::vector<expected_type_info> m_expected_type_info;

    info_ref mk_app_mismatch_info(expr const & app, context const & ctx, unsigned sz, expr const * args, expr const * types) {
        unsigned idx = m_app_mismatch_info.size();
        m_app_mismatch_info.push_back(app_mismatch_info(app, ctx, sz, args, types));
        return mk_pair(info_kind::AppMismatchInfo, idx);
    }

    info_ref mk_expected_type_info(expr const & e, expr const & p, expr const & exp, expr const & g, context const & ctx) {
        unsigned idx = m_expected_type_info.size();
        m_expected_type_info.push_back(expected_type_info(e, p, exp, g, ctx));
        return mk_pair(info_kind::ExpectedTypeInfo, idx);
    }

    context get_context(info_ref const & r) const {
        if (r.first == info_kind::AppMismatchInfo)
            return m_app_mismatch_info[r.second].m_ctx;
        else
            return m_expected_type_info[r.second].m_ctx;
    }

    // unification constraint lhs == second
    struct constraint {
        expr     m_lhs;
        expr     m_rhs;
        context  m_ctx;
        info_ref m_info;
        constraint(expr const & lhs, expr const & rhs, context const & ctx, info_ref const & r):
            m_lhs(lhs), m_rhs(rhs), m_ctx(ctx), m_info(r) {}
        constraint(expr const & lhs, expr const & rhs, constraint const & c):
            m_lhs(lhs), m_rhs(rhs), m_ctx(c.m_ctx), m_info(c.m_info) {}
        constraint(expr const & lhs, expr const & rhs, context const & ctx, constraint const & c):
            m_lhs(lhs), m_rhs(rhs), m_ctx(ctx), m_info(c.m_info) {}
    };

    // information associated with the metavariable
    struct metavar_info {
        expr    m_assignment;
        expr    m_type;
        expr    m_mvar;
        context m_ctx;
        bool    m_mark;       // for implementing occurs check
        bool    m_type_cnstr; // true when type constraint was already generated
        metavar_info() {
            m_mark = false;
            m_type_cnstr = false;
        }
    };

    typedef std::deque<constraint>    constraint_queue;
    typedef std::vector<metavar_info> metavars;

    frontend  const &   m_frontend;
    environment const & m_env;
    name_set const *    m_available_defs;
    elaborator const *  m_owner;
    expr                m_root;

    constraint_queue    m_constraints;
    metavars            m_metavars;

    normalizer          m_normalizer;

    bool                m_processing_root;

    // The following mapping is used to store the relationship
    // between elaborated expressions and non-elaborated expressions.
    // We need that because a frontend may associate line number information
    // with the original non-elaborated expressions.
    expr_map<expr>      m_trace;

    volatile bool       m_interrupted;

    void add_trace(expr const & old_e, expr const & new_e) {
        if (!is_eqp(old_e, new_e)) {
            m_trace[new_e] = old_e;
        }
    }

    expr mk_metavar(context const & ctx) {
        unsigned midx = m_metavars.size();
        expr r = ::lean::mk_metavar(midx);
        m_metavars.push_back(metavar_info());
        m_metavars[midx].m_mvar = r;
        m_metavars[midx].m_ctx  = ctx;
        return r;
    }

    expr metavar_type(expr const & m) {
        lean_assert(is_metavar(m));
        unsigned midx = metavar_idx(m);
        if (m_metavars[midx].m_type) {
            return m_metavars[midx].m_type;
        } else {
            context ctx = m_metavars[midx].m_ctx;
            expr t = mk_metavar(ctx);
            m_metavars[midx].m_type = t;
            return t;
        }
    }

    expr lookup(context const & c, unsigned i) {
        auto p = lookup_ext(c, i);
        context_entry const & def = p.first;
        context const & def_c     = p.second;
        lean_assert(c.size() > def_c.size());
        return lift_free_vars(def.get_domain(), 0, c.size() - def_c.size());
    }

    expr check_pi(expr const & e, context const & ctx, expr const & s, context const & s_ctx) {
        check_interrupted(m_interrupted);
        if (is_pi(e)) {
            return e;
        } else {
            expr r = head_reduce(e, m_env, ctx, m_available_defs);
            if (!is_eqp(r, e)) {
                return check_pi(r, ctx, s, s_ctx);
            } else if (is_var(e)) {
                try {
                    auto p = lookup_ext(ctx, var_idx(e));
                    context_entry const & entry = p.first;
                    context const & entry_ctx   = p.second;
                    if (entry.get_body()) {
                        return lift_free_vars(check_pi(entry.get_body(), entry_ctx, s, s_ctx), 0, ctx.size() - entry_ctx.size());
                    }
                } catch (exception&) {
                    // this can happen if we access a variable out of scope
                    throw function_expected_exception(m_env, s_ctx, s);
                }
            } else if (has_assigned_metavar(e)) {
                return check_pi(instantiate(e), ctx, s, s_ctx);
            } else if (is_metavar(e) && !has_meta_context(e)) {
                // e is a unassigned metavariable that must be a Pi,
                // then we can assign it to (Pi x : A, B x), where
                // A and B are fresh metavariables
                unsigned midx = metavar_idx(e);
                expr A = mk_metavar(ctx);
                name x("x");
                context ctx2 = extend(ctx, x, A);
                expr B = mk_metavar(ctx2);
                expr type = mk_pi(x, A, B(Var(0)));
                m_metavars[midx].m_assignment = type;
                return type;
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
        } else if (e == Bool) {
            return level();
        } else {
            expr r = head_reduce(e, m_env, ctx, m_available_defs);
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
            } else if (has_assigned_metavar(e)) {
                return check_universe(instantiate(e), ctx, s, s_ctx);
            }
            throw type_expected_exception(m_env, s_ctx, s);
        }
    }

    bool is_convertible(expr const & t1, expr const & t2, context const & ctx) {
        return m_normalizer.is_convertible(t1, t2, ctx);
    }

    void choose(buffer<expr> const & f_choices, buffer<expr> const & f_choice_types,
                buffer<expr> & args, buffer<expr> & types,
                context const & ctx, expr const & src) {
        lean_assert(f_choices.size() == f_choice_types.size());
        buffer<unsigned> good_choices;
        unsigned best_num_coercions = std::numeric_limits<unsigned>::max();
        unsigned num_choices = f_choices.size();
        unsigned num_args    = args.size();
        // We consider two overloads ambiguous if they need the same number of coercions.
        for (unsigned j = 0; j < num_choices; j++) {
            expr f_t = f_choice_types[j];
            unsigned num_coercions = 0; // number of coercions needed by current choice
            try {
                unsigned i = 1;
                for (; i < num_args; i++) {
                    f_t = check_pi(f_t, ctx, src, ctx);
                    expr expected = abst_domain(f_t);
                    expr given    = types[i];
                    if (!has_metavar(expected) && !has_metavar(given)) {
                        if (is_convertible(given, expected, ctx)) {
                            // compatible
                        } else if (m_frontend.get_coercion(given, expected, ctx)) {
                            // compatible if using coercion
                            num_coercions++;
                        } else {
                            break; // failed
                        }
                    }
                    f_t = ::lean::instantiate(abst_body(f_t), args[i]);
                }
                if (i == num_args) {
                    if (num_coercions < best_num_coercions) {
                        // found best choice
                        args[0]  = f_choices[j];
                        types[0] = f_choice_types[j];
                        good_choices.clear();
                        best_num_coercions = num_coercions;
                    }
                    good_choices.push_back(j);
                }
            } catch (exception & ex) {
                // candidate failed
                // do nothing
            }
        }
        if (good_choices.size() == 0) {
            throw no_overload_exception(*m_owner, ctx, src, f_choices.size(), f_choices.data(), f_choice_types.data(),
                                        args.size() - 1, args.data() + 1, types.data() + 1);
        } else if (good_choices.size() == 1) {
            // found overload
            return;
        } else {
            buffer<expr> good_f_choices;
            buffer<expr> good_f_choice_types;
            for (unsigned j : good_choices) {
                good_f_choices.push_back(f_choices[j]);
                good_f_choice_types.push_back(f_choice_types[j]);
            }
            throw ambiguous_overload_exception(*m_owner, ctx, src, good_f_choices.size(), good_f_choices.data(), good_f_choice_types.data(),
                                               args.size() - 1, args.data() + 1, types.data() + 1);
        }
    }

    /**
       \brief Traverse the expression \c e, and compute

       1- A new expression that does not contain choice expressions,
       coercions have been added when appropriate, and placeholders
       have been replaced with metavariables.

       2- The type of \c e.

       It also populates m_constraints with a set of constraints that
       need to be solved to infer the value of the metavariables.
    */
    expr_pair process(expr const & e, context const & ctx) {
        check_interrupted(m_interrupted);
        switch (e.kind()) {
        case expr_kind::MetaVar:
            return expr_pair(e, metavar_type(e));
        case expr_kind::Constant:
            if (is_placeholder(e)) {
                expr m = mk_metavar(ctx);
                m_trace[m] = e;
                return expr_pair(m, metavar_type(m));
            } else {
                return expr_pair(e, m_env.get_object(const_name(e)).get_type());
            }
        case expr_kind::Var:
            return expr_pair(e, lookup(ctx, var_idx(e)));
        case expr_kind::Type:
            return expr_pair(e, mk_type(ty_level(e) + 1));
        case expr_kind::Value:
            return expr_pair(e, to_value(e).get_type());
        case expr_kind::App: {
            buffer<expr> args;
            buffer<expr> types;
            buffer<expr> f_choices;
            buffer<expr> f_choice_types;
            unsigned num = num_args(e);
            unsigned i = 0;
            bool modified = false;
            expr const & f = arg(e, 0);
            if (is_metavar(f)) {
                throw invalid_placeholder_exception(*m_owner, ctx, e);
            } else if (is_choice(f)) {
                unsigned num_alts = get_num_choices(f);
                for (unsigned j = 0; j < num_alts; j++) {
                    auto p = process(get_choice(f, j), ctx);
                    f_choices.push_back(p.first);
                    f_choice_types.push_back(p.second);
                }
                args.push_back(expr()); // placeholder
                types.push_back(expr()); // placeholder
                modified = true;
                i++;
            }
            for (; i < num; i++) {
                expr const & a_i = arg(e, i);
                auto p = process(a_i, ctx);
                if (!is_eqp(p.first, a_i))
                    modified = true;
                args.push_back(p.first);
                types.push_back(p.second);
            }
            if (!f_choices.empty()) {
                // choose one of the functions (overloads) based on the types in types
                choose(f_choices, f_choice_types, args, types, ctx, e);
            }
            expr f_t = types[0];
            for (unsigned i = 1; i < num; i++) {
                f_t = check_pi(f_t, ctx, e, ctx);
                if (m_processing_root) {
                    expr expected = abst_domain(f_t);
                    expr given    = types[i];
                    if (has_metavar(expected) || has_metavar(given)) {
                        info_ref r = mk_app_mismatch_info(e, ctx, args.size(), args.data(), types.data());
                        m_constraints.push_back(constraint(expected, given, ctx, r));
                    } else {
                        if (!is_convertible(given, expected, ctx)) {
                            expr coercion = m_frontend.get_coercion(given, expected, ctx);
                            if (coercion) {
                                modified = true;
                                args[i] = mk_app(coercion, args[i]);
                            } else {
                                throw app_type_mismatch_exception(m_env, ctx, e, types.size(), types.data());
                            }
                        }
                    }
                }
                f_t = ::lean::instantiate(abst_body(f_t), args[i]);
            }
            if (modified) {
                expr new_e = mk_app(args.size(), args.data());
                m_trace[new_e] = e;
                return expr_pair(new_e, f_t);
            } else {
                return expr_pair(e, f_t);
            }
        }
        case expr_kind::Eq: {
            auto lhs_p = process(eq_lhs(e), ctx);
            auto rhs_p = process(eq_rhs(e), ctx);
            expr new_e = update_eq(e, lhs_p.first, rhs_p.first);
            add_trace(e, new_e);
            return expr_pair(new_e, mk_bool_type());
        }
        case expr_kind::Pi: {
            auto d_p = process(abst_domain(e), ctx);
            auto b_p = process(abst_body(e), extend(ctx, abst_name(e), d_p.first));
            expr t   = mk_type(max(check_universe(d_p.second, ctx, e, ctx), check_universe(b_p.second, ctx, e, ctx)));
            expr new_e = update_pi(e, d_p.first, b_p.first);
            add_trace(e, new_e);
            return expr_pair(new_e, t);
        }
        case expr_kind::Lambda: {
            auto d_p = process(abst_domain(e), ctx);
            auto b_p = process(abst_body(e), extend(ctx, abst_name(e), d_p.first));
            expr t   = mk_pi(abst_name(e), d_p.first, b_p.second);
            expr new_e = update_lambda(e, d_p.first, b_p.first);
            add_trace(e, new_e);
            return expr_pair(new_e, t);
        }
        case expr_kind::Let: {
            expr_pair t_p;
            if (let_type(e))
                 t_p = process(let_type(e), ctx);
            auto v_p = process(let_value(e), ctx);
            if (let_type(e)) {
                expr const & expected = t_p.first;
                expr const & given    = v_p.second;
                if (has_metavar(expected) || has_metavar(given)) {
                    info_ref r = mk_expected_type_info(let_value(e), v_p.first, expected, given, ctx);
                    m_constraints.push_back(constraint(expected, given, ctx, r));
                } else {
                    if (!is_convertible(given, expected, ctx)) {
                        expr coercion = m_frontend.get_coercion(given, expected, ctx);
                        if (coercion) {
                            v_p.first = mk_app(coercion, v_p.first);
                        } else {
                            throw def_type_mismatch_exception(m_env, ctx, let_name(e), let_type(e), v_p.first, v_p.second);
                        }
                    }
                }
            }
            auto b_p = process(let_body(e), extend(ctx, let_name(e), t_p.first ? t_p.first : v_p.second, v_p.first));
            expr t   = ::lean::instantiate(b_p.second, v_p.first);
            expr new_e = update_let(e, t_p.first, v_p.first, b_p.first);
            add_trace(e, new_e);
            return expr_pair(new_e, t);
        }}
        lean_unreachable();
        return expr_pair(expr(), expr());
    }

    expr infer(expr const & e, context const & ctx) {
        return process(e, ctx).second;
    }

    bool is_simple_ho_match(expr const & e1, expr const & e2, context const & ctx) {
        if (is_app(e1) && is_metavar(arg(e1, 0)) && is_var(arg(e1, 1), 0) && num_args(e1) == 2 && !empty(ctx)) {
            return true;
        } else {
            return false;
        }
    }

    void unify_simple_ho_match(expr const & e1, expr const & e2, constraint const & c) {
        context const & ctx = c.m_ctx;
        context_entry const & head = ::lean::lookup(ctx, 0);
        m_constraints.push_back(constraint(arg(e1, 0), mk_lambda(head.get_name(),
                                                           lift_free_vars(head.get_domain(), 1, 1),
                                                           lift_free_vars(e2, 1, 1)), c));
    }

    struct cycle_detected {};
    void occ_core(expr const & t) {
        check_interrupted(m_interrupted);
        auto proc = [&](expr const & e, unsigned) {
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
        info_ref const & r = c.m_info;
        if (r.first == info_kind::AppMismatchInfo) {
            app_mismatch_info & info = m_app_mismatch_info[r.second];
            for (expr & arg : info.m_args)
                arg = instantiate(arg);
            for (expr & type : info.m_types)
                type = instantiate(type);
            throw unification_app_mismatch_exception(*m_owner, info.m_ctx, info.m_app, info.m_args, info.m_types);
        } else {
            expected_type_info & info = m_expected_type_info[r.second];
            info.m_processed_expr = instantiate(info.m_processed_expr);
            info.m_given          = instantiate(info.m_given);
            info.m_expected       = instantiate(info.m_expected);
            throw unification_type_mismatch_exception(*m_owner, info.m_ctx, info.m_expr, info.m_processed_expr,
                                                      info.m_expected, info.m_given);
        }
    }

    void solve_mvar(expr const & m, expr const & t, constraint const & c) {
        lean_assert(is_metavar(m) && !has_meta_context(m));
        unsigned midx = metavar_idx(m);
        if (m_metavars[midx].m_assignment) {
            m_constraints.push_back(constraint(m_metavars[midx].m_assignment, t, c));
        } else if (has_metavar(t, midx) || !occ(t, midx)) {
            throw_unification_exception(c);
        } else {
            m_metavars[midx].m_assignment = t;
        }
    }

    /**
       \brief Temporary hack until we build the new elaborator.
    */
    expr instantiate_metavar(expr const & e, unsigned midx, expr const & v) {
        metavar_env menv;
        while (!menv.contains(midx))
            menv.mk_metavar();
        menv.assign(midx, v);
        return instantiate_metavars(e, menv);
    }

    /**
       \brief Temporary hack until we build the new elaborator.
    */
    bool is_lift(expr const & e, expr & c, unsigned & s, unsigned & n) {
        if (!is_metavar(e) || !has_meta_context(e))
            return false;
        meta_ctx const & ctx = metavar_ctx(e);
        meta_entry const & entry = head(ctx);
        if (entry.is_lift()) {
            c = ::lean::mk_metavar(metavar_idx(e), tail(ctx));
            add_trace(e, c);
            s = entry.s();
            n = entry.n();
            return true;
        } else {
            return false;
        }
    }

    /**
       \brief Temporary hack until we build the new elaborator.
    */
    bool is_inst(expr const & e, expr & c, unsigned & s, expr & v) {
        if (!is_metavar(e) || !has_meta_context(e))
            return false;
        meta_ctx const & ctx = metavar_ctx(e);
        meta_entry const & entry = head(ctx);
        if (entry.is_inst()) {
            c = ::lean::mk_metavar(metavar_idx(e), tail(ctx));
            add_trace(e, c);
            s = entry.s();
            v = entry.v();
            return true;
        } else {
            return false;
        }
    }

    bool solve_meta(expr const & e, expr const & t, constraint const & c) {
        lean_assert(has_meta_context(e));
        expr const & m = e;
        unsigned midx  = metavar_idx(m);
        unsigned i, s, n;
        expr v, a, b;

        if (m_metavars[midx].m_assignment) {
            expr s = instantiate_metavar(e, midx, m_metavars[midx].m_assignment);
            m_constraints.push_back(constraint(s, t, c));
            return true;
        }

        if (!has_metavar(t)) {
            if (is_lift(e, a, s, n)) {
                if (!has_free_var(t, s, s+n)) {
                    m_constraints.push_back(constraint(a, lower_free_vars(t, s+n, n), c));
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

        if (is_inst(e, a, i, v) && is_lift(a, b, s, n) && !has_free_var(t, s, s+n)) {
            // subst (lift b s n) i v  ==  t
            // t does not have free-variables in the range [s, s+n)
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
            } else if (is_metavar(lhs) && !has_meta_context(lhs)) {
                delayed = 0;
                solve_mvar(lhs, rhs, c);
            } else if (is_metavar(rhs) && !has_meta_context(rhs)) {
                delayed = 0;
                solve_mvar(rhs, lhs, c);
            } else if (is_metavar(lhs) || is_metavar(rhs)) {
                if (is_metavar(lhs) && solve_meta(lhs, rhs, c)) {
                    delayed = 0;
                } else if (is_metavar(rhs) && solve_meta(rhs, lhs, c)) {
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
                // ignoring type universe levels. We let the kernel check that
                delayed = 0;
            } else if (is_abstraction(lhs) && is_abstraction(rhs)) {
                delayed = 0;
                m_constraints.push_back(constraint(abst_domain(lhs), abst_domain(rhs), c));
                m_constraints.push_back(constraint(abst_body(lhs),   abst_body(rhs), extend(c.m_ctx, abst_name(lhs), abst_domain(lhs)), c));
            } else if (is_eq(lhs) && is_eq(rhs)) {
                delayed = 0;
                m_constraints.push_back(constraint(eq_lhs(lhs), eq_lhs(rhs), c));
                m_constraints.push_back(constraint(eq_rhs(lhs), eq_rhs(rhs), c));
            } else {
                expr new_lhs = head_reduce(lhs, m_env, c.m_ctx, m_available_defs);
                expr new_rhs = head_reduce(rhs, m_env, c.m_ctx, m_available_defs);
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
                } else if (has_assigned_metavar(new_lhs)) {
                    delayed = 0;
                    m_constraints.push_back(constraint(instantiate(new_lhs), new_rhs, c));
                } else if (has_assigned_metavar(new_rhs)) {
                    delayed = 0;
                    m_constraints.push_back(constraint(new_lhs, instantiate(new_rhs), c));
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
            }
        }
    }

    struct found_assigned {};
    bool has_assigned_metavar(expr const & e) {
        auto proc = [&](expr const & n, unsigned) {
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
        auto proc = [&](expr const & n, unsigned) -> expr {
            if (is_metavar(n)) {
                expr const & m = n;
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

        auto tracer = [&](expr const & old_e, expr const & new_e) {
            add_trace(old_e, new_e);
        };

        replace_fn<decltype(proc), decltype(tracer)> replacer(proc, tracer);
        return replacer(e);
    }

    void solve() {
        unsigned num_meta = m_metavars.size();
        m_processing_root = false;
        while (true) {
            solve_core();
            bool cont     = false;
            bool progress = false;
            // unsigned unsolved_midx = 0;
            for (unsigned midx = 0; midx < num_meta; midx++) {
                if (m_metavars[midx].m_assignment) {
                    if (has_assigned_metavar(m_metavars[midx].m_assignment)) {
                        m_metavars[midx].m_assignment = instantiate(m_metavars[midx].m_assignment);
                    }
                    if (has_metavar(m_metavars[midx].m_assignment)) {
                        // unsolved_midx = midx;
                        cont = true; // must continue
                    } else {
                        if (m_metavars[midx].m_type && !m_metavars[midx].m_type_cnstr) {
                            context ctx = m_metavars[midx].m_ctx;
                            try {
                                expr t = infer(m_metavars[midx].m_assignment, ctx);
                                m_metavars[midx].m_type_cnstr = true;
                                info_ref r = mk_expected_type_info(m_metavars[midx].m_mvar, m_metavars[midx].m_assignment,
                                                                   m_metavars[midx].m_type, t, ctx);
                                m_constraints.push_back(constraint(m_metavars[midx].m_type, t, ctx, r));
                                progress = true;
                            } catch (exception&) {
                                // std::cout << "Failed to infer type of: ?M" << midx << "\n"
                                //           << m_metavars[midx].m_assignment << "\nAT\n" << m_metavars[midx].m_ctx << "\n";
                                expr null_given_type; // failed to infer given type.
                                throw unification_type_mismatch_exception(*m_owner, ctx, m_metavars[midx].m_mvar, m_metavars[midx].m_assignment,
                                                                          instantiate(m_metavars[midx].m_type), null_given_type);
                            }
                        }
                    }
                } else {
                    cont = true;
                }
            }
            if (!cont)
                return;
            if (!progress)
                return;
        }
    }

public:
    imp(frontend const & fe, name_set const * defs):
        m_frontend(fe),
        m_env(fe.get_environment()),
        m_available_defs(defs),
        m_normalizer(m_env) {
        m_interrupted = false;
        m_owner = nullptr;
    }

    void clear() {
        m_trace.clear();
        m_normalizer.clear();
    }

    void set_interrupt(bool flag) {
        m_interrupted = flag;
        m_normalizer.set_interrupt(flag);
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

    expr operator()(expr const & e, expr const & expected_type, elaborator const & elb) {
        m_owner = &elb;
        m_constraints.clear();
        m_metavars.clear();
        m_app_mismatch_info.clear();
        m_expected_type_info.clear();
        m_processing_root = true;
        auto p = process(e, context());
        m_root = p.first;
        expr given_type = p.second;
        if (expected_type) {
            if (has_metavar(given_type)) {
                info_ref r = mk_expected_type_info(e, m_root, expected_type, given_type, context());
                m_constraints.push_back(constraint(expected_type, given_type, context(), r));
            }
        }
        if (has_metavar(m_root)) {
            solve();
            expr r = instantiate(m_root);
            if (has_metavar(r))
                throw unsolved_placeholder_exception(elb, context(), m_root);
            return r;
        } else {
            return m_root;
        }
    }

    expr const & get_original(expr const & e) const {
        expr const * r = &e;
        while (true) {
            auto it = m_trace.find(*r);
            if (it == m_trace.end()) {
                return *r;
            } else {
                r = &(it->second);
            }
        }
    }

    format pp(formatter & f, options const & o) const {
        bool unicode = get_pp_unicode(o);
        format r;
        bool first = true;
        for (auto c : m_constraints) {
            if (first) first = false; else r += line();
            r += group(format{f(c.m_lhs, o), space(), unicode ? g_unification_u_fmt : g_unification_fmt, line(), f(c.m_rhs, o)});
        }
        return r;
    }

    bool has_constraints() const { return !m_constraints.empty(); }
};
elaborator::elaborator(frontend const & fe):m_ptr(new imp(fe, nullptr)) {}
elaborator::~elaborator() {}
expr elaborator::operator()(expr const & e) { return (*m_ptr)(e, expr(), *this); }
expr elaborator::operator()(expr const & e, expr const & expected_type) { return (*m_ptr)(e, expected_type, *this); }
expr const & elaborator::get_original(expr const & e) const { return m_ptr->get_original(e); }
void elaborator::set_interrupt(bool flag) { m_ptr->set_interrupt(flag); }
void elaborator::clear() { m_ptr->clear(); }
environment const & elaborator::get_environment() const { return m_ptr->get_environment(); }
void elaborator::display(std::ostream & out) const { m_ptr->display(out); }
format elaborator::pp(formatter & f, options const & o) const { return m_ptr->pp(f, o); }
void elaborator::print(imp * ptr) { ptr->display(std::cout); }
bool elaborator::has_constraints() const { return m_ptr->has_constraints(); }
}
