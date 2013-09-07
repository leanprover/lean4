/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "printer.h"
#include "metavar.h"
#include "environment.h"
#include "exception.h"

namespace lean {
bool is_atomic(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var: case expr_kind::Constant: case expr_kind::Value: case expr_kind::Type:
        return true;
    case expr_kind::App: case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Eq: case expr_kind::Let:
        return false;
    }
    return false;
}

/**
   \brief Very basic printer for expressions.
   It is mainly used when debugging code.
*/
struct print_expr_fn {
    std::ostream & m_out;

    std::ostream & out() { return m_out; }

    void print_child(expr const & a, context const & c) {
        if (is_atomic(a)) {
            print(a, c);
        } else {
            out() << "(";
            print(a, c);
            out() << ")";
        }
    }

    void print_value(expr const & a) {
        to_value(a).display(out());
    }

    void print_type(expr const & a) {
        if (a == Type()) {
            out() << "Type";
        } else {
            out() << "Type " << ty_level(a);
        }
    }

    void print_eq(expr const & a, context const & c) {
        print_child(eq_lhs(a), c);
        out() << " = ";
        print_child(eq_rhs(a), c);
    }

    void print_app(expr const & e, context const & c) {
        print_child(arg(e, 0), c);
        for (unsigned i = 1; i < num_args(e); i++) {
            out() << " ";
            print_child(arg(e, i), c);
        }
    }

    void print_arrow_body(expr const & a, context const & c) {
        if (is_atomic(a) || is_arrow(a))
            return print(a, c);
        else
            return print_child(a, c);
    }

    void print(expr const & a, context const & c) {
        unsigned i, s, n;
        expr v, ch;
        if (is_lower(a, ch, s, n)) {
            out() << "lower:" << s << ":" << n << " "; print_child(ch, c);
        } else if (is_lift(a, ch, s, n)) {
            out() << "lift:" << s << ":" << n << " "; print_child(ch, c);
        } else if (is_subst(a, ch, i, v)) {
            out() << "subst:" << i << " "; print_child(ch, c); out() << " "; print_child(v, context());
        } else {
            switch (a.kind()) {
            case expr_kind::Var:
                try {
                    out() << lookup(c, var_idx(a)).get_name();
                } catch (exception & ex) {
                    out() << "#" << var_idx(a);
                }
                break;
            case expr_kind::Constant:
                if (is_metavar(a)) {
                    out() << "?M:" << metavar_idx(a);
                } else {
                    out() << const_name(a);
                }
                break;
            case expr_kind::App:
                print_app(a, c);
                break;
            case expr_kind::Eq:
                print_eq(a, c);
                break;
            case expr_kind::Lambda:
                out() << "fun " << abst_name(a) << " : ";
                print_child(abst_domain(a), c);
                out() << ", ";
                print_child(abst_body(a), extend(c, abst_name(a), abst_domain(a)));
                break;
            case expr_kind::Pi:
                if (!is_arrow(a)) {
                    out() << "Pi " << abst_name(a) << " : ";
                    print_child(abst_domain(a), c);
                    out() << ", ";
                    print_child(abst_body(a), extend(c, abst_name(a), abst_domain(a)));
                    break;
                } else {
                    print_child(abst_domain(a), c);
                    out() << " -> ";
                    print_arrow_body(abst_body(a), extend(c, abst_name(a), abst_domain(a)));
                }
                break;
            case expr_kind::Let:
                out() << "let " << let_name(a);
                if (let_type(a))
                    out() << " : " << let_type(a);
                out() << " := ";
                print(let_value(a), c);
                out() << " in ";
                print_child(let_body(a), extend(c, let_name(a), let_value(a)));
                break;
            case expr_kind::Type:
                print_type(a);
                break;
            case expr_kind::Value:
                print_value(a);
                break;
            }
        }
    }

    print_expr_fn(std::ostream & out):m_out(out) {}

    void operator()(expr const & e, context const & c) {
        print(e, c);
    }
};

std::ostream & operator<<(std::ostream & out, expr const & e) {
    print_expr_fn pr(out);
    pr(e, context());
    return out;
}

std::ostream & operator<<(std::ostream & out, std::pair<expr const &, context const &> const & p) {
    print_expr_fn pr(out);
    pr(p.first, p.second);
    return out;
}

static void display_context_core(std::ostream & out, context const & ctx) {
    if (!is_empty(ctx)) {
        auto p = lookup_ext(ctx, 0);
        context_entry const & head  = p.first;
        context const & tail_ctx    = p.second;
        display_context_core(out, tail_ctx);
        if (!is_empty(tail_ctx))
            out << "; ";
        out << head.get_name() << " : " << head.get_domain();
        if (head.get_body()) {
            out << " := " << mk_pair(head.get_body(), tail_ctx);
        }
    }
}

std::ostream & operator<<(std::ostream & out, context const & ctx) {
    out << "[";
    display_context_core(out, ctx);
    out << "]";
    return out;
}

std::ostream & operator<<(std::ostream & out, object const & obj) {
    out << obj.keyword() << " ";
    switch (obj.kind()) {
    case object_kind::UVarDeclaration:
        out << obj.get_name() << " >= " << obj.get_cnstr_level(); break;
    case object_kind::Postulate:
        out << obj.get_name() << " : " << obj.get_type(); break;
    case object_kind::Definition: case object_kind::Builtin:
        out << obj.get_name() << " : " << obj.get_type() << " :=\n    " << obj.get_value(); break;
    case object_kind::BuiltinSet:
        out << obj.get_name(); break;
    case object_kind::Neutral:
        break;
    }
    return out;
}

std::ostream & operator<<(std::ostream & out, environment const & env) {
    std::for_each(env.begin_objects(),
                  env.end_objects(),
                  [&](object const & obj) { out << obj << "\n"; });
    return out;
}
}
void print(lean::expr const & a) { std::cout << a << std::endl; }
void print(lean::expr const & a, lean::context const & c) { std::cout << mk_pair(a, c) << std::endl; }
void print(lean::context const & c) { std::cout << c << std::endl; }
void print(lean::environment const & e) { std::cout << e << std::endl; }
