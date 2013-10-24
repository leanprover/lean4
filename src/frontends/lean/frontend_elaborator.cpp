/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <utility>
#include "util/interruptable_ptr.h"
#include "kernel/type_checker.h"
#include "kernel/type_checker_justification.h"
#include "kernel/normalizer.h"
#include "kernel/replace_visitor.h"
#include "kernel/unification_constraint.h"
#include "kernel/instantiate.h"
#include "library/type_inferer.h"
#include "library/placeholder.h"
#include "library/elaborator/elaborator.h"
#include "frontends/lean/frontend.h"
#include "frontends/lean/frontend_elaborator.h"

namespace lean {
static name g_x_name("x");
static name g_choice_name = name::mk_internal_unique_name();
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

class coercion_justification_cell : public justification_cell {
    context m_ctx;
    expr    m_app;
    expr    m_arg;
public:
    coercion_justification_cell(context const & c, expr const & app, expr const & arg):m_ctx(c), m_app(app), m_arg(arg) {}
    virtual ~coercion_justification_cell() {}
    virtual format pp_header(formatter const & fmt, options const & opts) const {
        unsigned indent = get_pp_indent(opts);
        format expr_fmt = fmt(m_ctx, m_arg, false, opts);
        format r;
        r += format("Coercion for");
        r += nest(indent, compose(line(), expr_fmt));
        return r;
    }
    virtual void get_children(buffer<justification_cell*> &) const {}
    virtual expr const & get_main_expr() const { return m_arg; }
    context const & get_context() const { return m_ctx; }
    expr const & get_app() const { return m_app; }
};

class overload_justification_cell : public justification_cell {
    context m_ctx;
    expr    m_app;
public:
    overload_justification_cell(context const & c, expr const & app):m_ctx(c), m_app(app) {}
    virtual ~overload_justification_cell() {}
    virtual format pp_header(formatter const & fmt, options const & opts) const {
        unsigned indent = get_pp_indent(opts);
        format expr_fmt = fmt(m_ctx, m_app, false, opts);
        format r;
        r += format("Overloading at");
        r += nest(indent, compose(line(), expr_fmt));
        return r;
    }
    virtual void get_children(buffer<justification_cell*> &) const {}
    virtual expr const & get_main_expr() const { return m_app; }
    context const & get_context() const { return m_ctx; }
    expr const & get_app() const { return m_app; }
};


inline justification mk_coercion_justification(context const & ctx, expr const & app, expr const & arg) {
    return justification(new coercion_justification_cell(ctx, app, arg));
}

inline justification mk_overload_justification(context const & ctx, expr const & app) {
    return justification(new overload_justification_cell(ctx, app));
}

/**
    \brief Actual implementation of the frontend_elaborator.
*/
class frontend_elaborator::imp {
    frontend  const &                   m_frontend;
    environment const &                 m_env;
    type_checker                        m_type_checker;
    type_inferer                        m_type_inferer;
    normalizer                          m_normalizer;
    metavar_env                         m_menv;
    buffer<unification_constraint>      m_ucs;
    // The following mapping is used to store the relationship
    // between elaborated expressions and non-elaborated expressions.
    // We need that because a frontend may associate line number information
    // with the original non-elaborated expressions.
    expr_map<expr>                      m_trace;
    interruptable_ptr<elaborator>       m_elaborator;
    volatile bool                       m_interrupted;

    /**
       \brief Replace placeholders and choices with metavariables.
       It also introduce metavariables where coercions are needed.
    */
    struct preprocessor : public replace_visitor {
        imp & m_ref;
        preprocessor(imp & r):m_ref(r) {}

        virtual expr visit_constant(expr const & e, context const & ctx) {
            if (is_placeholder(e)) {
                expr m = m_ref.m_menv.mk_metavar(ctx);
                m_ref.m_trace[m] = e;
                return m;
            } else {
                return e;
            }
        }

        /**
           \brief Return the type of \c e if possible.
           Return null expression if it was not possible to infer the type of \c e.
           The idea is to use the type to catch the easy cases where we can solve
           overloads (aka choices) and coercions during preprocessing.
        */
        expr get_type(expr const & e, context const & ctx) {
            try {
                return m_ref.m_type_inferer(e, ctx);
            } catch (exception &) {
                return expr();
            }
        }

        /**
           \brief Make sure f_t is a Pi, if it is not, then return the null expression.
        */
        expr check_pi(expr const & f_t, context const & ctx) {
            if (!f_t || is_pi(f_t)) {
                return f_t;
            } else {
                expr r = m_ref.m_normalizer(f_t, ctx);
                if (is_pi(r))
                    return r;
                else
                    return expr();
            }
        }

        expr add_coercion_mvar_app(list<expr_pair> const & l, expr const & a, expr const & a_t,
                                   context const & ctx, expr const & original_app, expr const & original_a) {
            buffer<expr> choices;
            expr mvar = m_ref.m_menv.mk_metavar(ctx);
            for (auto p : l) {
                choices.push_back(p.second);
            }
            choices.push_back(mk_lambda(g_x_name, a_t, mk_var(0))); // add indentity function
            std::reverse(choices.begin(), choices.end());
            m_ref.m_ucs.push_back(mk_choice_constraint(ctx, mvar, choices.size(), choices.data(),
                                                       mk_coercion_justification(ctx, original_app, original_a)));
            return mk_app(mvar, a);
        }

        expr find_coercion(list<expr_pair> const & l, expr const & to_type) {
            for (auto p : l) {
                if (p.first == to_type)
                    return p.second;
            }
            return expr();
        }

        /**
           \brief Try to solve overload at preprocessing time.
        */
        bool choose(buffer<expr> const & f_choices, buffer<expr> const & f_choice_types,
                    buffer<expr> & args, buffer<expr> & arg_types,
                    context const & ctx, expr const & src) {
            // TODO(Leo)
            return false;
        }

        /**
           \brief Create a metavariable for representing the choice.
        */
        expr mk_overload_mvar(buffer<expr> & f_choices, context const & ctx, expr const & src) {
            std::reverse(f_choices.begin(), f_choices.end());
            expr mvar = m_ref.m_menv.mk_metavar(ctx);
            m_ref.m_ucs.push_back(mk_choice_constraint(ctx, mvar, f_choices.size(), f_choices.data(),
                                                       mk_overload_justification(ctx, src)));
            return mvar;
        }

        virtual expr visit_app(expr const & e, context const & ctx) {
            expr const & f = arg(e, 0);
            if (is_choice(f)) {
                buffer<expr> f_choices;
                buffer<expr> f_choice_types;
                buffer<expr> args;
                buffer<expr> arg_types;
                unsigned num_alts = get_num_choices(f);
                for (unsigned i = 0; i < num_alts; i++) {
                    expr c       = get_choice(f, i);
                    expr new_c   = visit(c, ctx);
                    expr new_c_t = get_type(new_c, ctx);
                    f_choices.push_back(new_c);
                    f_choice_types.push_back(new_c_t);
                }
                args.push_back(expr());      // placeholder
                arg_types.push_back(expr()); // placeholder
                for (unsigned i = 1; i < num_args(e); i++) {
                    expr a = arg(e, i);
                    expr new_a   = visit(a, ctx);
                    expr new_a_t = get_type(new_a, ctx);
                    args.push_back(new_a);
                    arg_types.push_back(new_a_t);
                }
                if (!choose(f_choices, f_choice_types, args, arg_types, ctx, e)) {
                    args[0] = mk_overload_mvar(f_choices, ctx, e);
                    for (unsigned i = 1; i < args.size(); i++) {
                        if (arg_types[i]) {
                            list<expr_pair> coercions = m_ref.m_frontend.get_coercions(arg_types[i]);
                            if (coercions)
                                args[i] = add_coercion_mvar_app(coercions, args[i], arg_types[i], ctx, e, arg(e, i));
                        }
                    }
                }
                return mk_app(args.size(), args.data());
            } else {
                buffer<expr> new_args;
                expr new_f   = visit(f, ctx);
                expr new_f_t = get_type(new_f, ctx);
                new_args.push_back(new_f);
                for (unsigned i = 1; i < num_args(e); i++) {
                    new_f_t = check_pi(new_f_t, ctx);
                    expr a       = arg(e, i);
                    expr new_a   = visit(a, ctx);
                    expr new_a_t = get_type(new_a, ctx);
                    if (new_a_t) {
                        list<expr_pair> coercions = m_ref.m_frontend.get_coercions(new_a_t);
                        if (coercions) {
                            if (!new_f_t) {
                                new_a = add_coercion_mvar_app(coercions, new_a, new_a_t, ctx, e, a);
                            } else {
                                expr expected = abst_domain(new_f_t);
                                if (expected != new_a_t) {
                                    expr c = find_coercion(coercions, expected);
                                    if (c)
                                        new_a = mk_app(c, new_a); // apply coercion
                                    else
                                        new_a = add_coercion_mvar_app(coercions, new_a, new_a_t, ctx, e, a);
                                }
                            }
                        }
                    }
                    new_args.push_back(new_a);
                    if (new_f_t)
                        new_f_t = ::lean::instantiate(abst_body(new_f_t), new_a);
                }
                return mk_app(new_args.size(), new_args.data());
            }
        }

        virtual expr visit(expr const & e, context const & ctx) {
            check_interrupted(m_ref.m_interrupted);
            expr r = replace_visitor::visit(e, ctx);
            if (!is_eqp(r, e))
                m_ref.m_trace[r] = e;
            return r;
        }
    };

    substitution elaborate_core() {
        elaborator elb(m_env, m_menv, m_ucs.size(), m_ucs.data());
        scoped_set_interruptable_ptr<elaborator> set(m_elaborator, &elb);
        return elb.next();
    }

public:
    imp(frontend const & fe):
        m_frontend(fe),
        m_env(fe.get_environment()),
        m_type_checker(m_env),
        m_type_inferer(m_env),
        m_normalizer(m_env) {
        m_interrupted = false;
    }

    expr elaborate(expr const & e) {
        // std::cout << "Elaborate " << e << "\n";
        clear();
        expr new_e = preprocessor(*this)(e);
        // std::cout << "After preprocessing\n" << new_e << "\n";
        if (has_metavar(new_e)) {
            m_type_checker.infer_type(new_e, context(), &m_menv, m_ucs);
            substitution s = elaborate_core();
            return instantiate_metavars(new_e, s);
        } else {
            return new_e;
        }
    }

    std::pair<expr, expr> elaborate(name const & n, expr const & t, expr const & e) {
        // std::cout << "Elaborate " << t << " : " << e << "\n";
        clear();
        expr new_t = preprocessor(*this)(t);
        expr new_e = preprocessor(*this)(e);
        // std::cout << "After preprocessing\n" << new_t << "\n" << new_e << "\n";
        if (has_metavar(new_e) || has_metavar(new_t)) {
            m_type_checker.infer_type(new_t, context(), &m_menv, m_ucs);
            expr new_e_t = m_type_checker.infer_type(new_e, context(), &m_menv, m_ucs);
            m_ucs.push_back(mk_convertible_constraint(context(), new_e_t, new_t,
                                                      mk_def_type_match_justification(context(), n, e)));
            // for (auto c : m_ucs) {
            //    formatter fmt = mk_simple_formatter();
            //    std::cout << c.pp(fmt, options(), nullptr, false) << "\n";
            // }
            substitution s = elaborate_core();
            // s.for_each([&](name const & n, expr const & v) {
            //        std::cout << n << " --> " << v << "\n";
            //    });
            return mk_pair(instantiate_metavars(new_t, s), instantiate_metavars(new_e, s));
        } else {
            return mk_pair(new_t, new_e);
        }
    }

    expr const & get_original(expr const & e) {
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

    void set_interrupt(bool f) {
        m_interrupted = f;
        m_type_checker.set_interrupt(f);
        m_type_inferer.set_interrupt(f);
        m_normalizer.set_interrupt(f);
        m_elaborator.set_interrupt(f);
    }

    void clear() {
        // TODO(Leo)
        m_menv = metavar_env();
        m_ucs.clear();
        m_trace.clear();
        m_type_checker.clear();
        m_type_inferer.clear();
        m_normalizer.clear();
    }

    environment const & get_environment() const {
        return m_env;
    }
};

frontend_elaborator::frontend_elaborator(frontend const & fe):m_ptr(new imp(fe)) {}
frontend_elaborator::~frontend_elaborator() {}
expr frontend_elaborator::operator()(expr const & e) { return m_ptr->elaborate(e); }
std::pair<expr, expr> frontend_elaborator::operator()(name const & n, expr const & t, expr const & e) { return m_ptr->elaborate(n, t, e); }
expr const & frontend_elaborator::get_original(expr const & e) const { return m_ptr->get_original(e); }
void frontend_elaborator::set_interrupt(bool f) { m_ptr->set_interrupt(f); }
void frontend_elaborator::clear() { m_ptr->clear(); }
environment const & frontend_elaborator::get_environment() const { return m_ptr->get_environment(); }
}
