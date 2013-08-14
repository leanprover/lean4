/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "expr_formatter.h"
#include "exception.h"

namespace lean {
void expr_formatter::pp(std::ostream & out, expr const & e, context const & c) {
    out << mk_pair(operator()(e, c), get_options());
}

void expr_formatter::pp(std::ostream & out, expr const & e) {
    pp(out, e, context());
}

format expr_formatter::nest(format const & f) {
    return ::lean::nest(get_pp_indent(get_options()), f);
}

bool is_atomic(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var: case expr_kind::Constant: case expr_kind::Value: case expr_kind::Type:
        return true;
    case expr_kind::App: case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Eq: case expr_kind::Let:
        return false;
    }
    return false;
}

class simple_expr_formatter : public expr_formatter {
    static thread_local std::ostream * m_out;

    std::ostream & out() { return *m_out; }

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

    void print_app(expr const & a, context const & c) {
        print_child(arg(a, 0), c);
        for (unsigned i = 1; i < num_args(a); i++) {
            out() << " ";
            print_child(arg(a, i), c);
        }
    }

    void print_arrow_body(expr const & a, context const & c) {
        if (is_atomic(a) || is_arrow(a))
            return print(a, c);
        else
            return print_child(a, c);
    }

    void print(expr const & a, context const & c) {
        switch (a.kind()) {
        case expr_kind::Var:
            try {
                out() << lookup(c, var_idx(a)).get_name();
            } catch (exception & ex) {
                out() << "#" << var_idx(a);
            }
            break;
        case expr_kind::Constant:
            out() << const_name(a);
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
            out() << "let " << let_name(a) << " := ";
            print_child(let_value(a), c);
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

public:
    virtual ~simple_expr_formatter() {}

    virtual format operator()(expr const & e, context const & c) {
        std::ostringstream s;
        m_out = &s;
        print(e, c);
        return format(s.str());
    }

    virtual bool has_location(expr const & e) const { return false; }

    virtual std::pair<unsigned, unsigned> get_location(expr const & e) const { return mk_pair(0,0); }

    virtual options get_options() const { return options(); }

    void print(std::ostream & out, expr const & a, context const & c) {
        m_out = &out;
        print(a, c);
    }
};
thread_local std::ostream * simple_expr_formatter::m_out = 0;

std::shared_ptr<expr_formatter> mk_simple_expr_formatter() {
    return std::shared_ptr<expr_formatter>(new simple_expr_formatter());
}

std::ostream & operator<<(std::ostream & out, std::pair<expr_formatter &, expr const &> const & p) {
    p.first.pp(out, p.second);
    return out;
}

static simple_expr_formatter g_simple_formatter;

std::ostream & operator<<(std::ostream & out, expr const & a) {
    g_simple_formatter.print(out, a, context());
    return out;
}
}
