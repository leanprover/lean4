/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "kernel/formatter.h"
#include "kernel/environment.h"
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "kernel/free_vars.h"

namespace lean {
bool is_used_name(expr const & t, name const & n) {
    return static_cast<bool>(
        find(t, [&](expr const & e, unsigned) {
                return (is_constant(e) && const_name(e) == n)  // t has a constant named n
                    || (is_local(e) && (mlocal_name(e) == n || local_pp_name(e) == n)); // t has a local constant named n
            }));
}

name pick_unused_name(expr const & t, name const & s) {
    name r = s;
    unsigned i = 1;
    while (is_used_name(t, r)) {
        r = name(s).append_after(i);
        i++;
    }
    return r;
}

std::pair<expr, expr> binding_body_fresh(expr const & b, bool preserve_type) {
    lean_assert(is_binding(b));
    name n = pick_unused_name(binding_body(b), binding_name(b));
    expr c = mk_local(n, preserve_type ? binding_domain(b) : expr());
    return mk_pair(instantiate(binding_body(b), c), c);
}

std::pair<expr, expr> let_body_fresh(expr const & l, bool preserve_type) {
    lean_assert(is_let(l));
    name n = pick_unused_name(let_body(l), let_name(l));
    expr c = mk_local(n, preserve_type ? let_type(l) : expr());
    return mk_pair(instantiate(let_body(l), c), c);
}

/**
   \brief Very basic printer for expressions.
   It is mainly used when debugging code.
*/
struct print_expr_fn {
    std::ostream & m_out;
    bool m_type0_as_bool;

    std::ostream & out() { return m_out; }

    bool is_atomic(expr const & a) {
        return ::lean::is_atomic(a) || is_mlocal(a);
    }

    void print_child(expr const & a) {
        if (is_atomic(a)) {
            print(a);
        } else {
            out() << "("; print(a); out() << ")";
        }
    }

    void print_macro(expr const & a) {
        macro_def(a).display(out());
        for (unsigned i = 0; i < macro_num_args(a); i++) {
            out() << " "; print_child(macro_arg(a, i));
        }
    }

    void print_sort(expr const & a) {
        if (is_zero(sort_level(a))) {
            if (m_type0_as_bool)
                out() << "Bool";
            else
                out() << "Type";
        } else if (m_type0_as_bool && is_one(sort_level(a))) {
            out() << "Type";
        } else {
            out() << "Type.{" << sort_level(a) << "}";
        }
    }

    void print_app(expr const & e) {
        expr const & f = app_fn(e);
        if (is_app(f))
            print(f);
        else
            print_child(f);
        out() << " ";
        print_child(app_arg(e));
    }

    void print_arrow_body(expr const & a) {
        if (is_atomic(a) || is_arrow(a))
            return print(a);
        else
            return print_child(a);
    }

    void print_let(expr const & a) {
        auto p = let_body_fresh(a);
        expr const & b = p.first;
        expr const & n = p.second;
        out() << "let " << n;
        out() << " : ";
        print(let_type(a));
        out() << " := ";
        print(let_value(a));
        out() << " in ";
        print_child(b);
    }

    void print_binding(char const * bname, expr e) {
        expr_kind k = e.kind();
        out() << bname;
        while (e.kind() == k) {
            out() << " ";
            auto p = binding_body_fresh(e);
            expr const & n = p.second;
            if (binding_info(e).is_implicit())
                out() << "{";
            else if (binding_info(e).is_cast())
                out() << "[";
            else if (!binding_info(e).is_contextual())
                out() << "[[";
            else
                out() << "(";
            out() << n << " : ";
            print(binding_domain(e));
            if (binding_info(e).is_implicit())
                out() << "}";
            else if (binding_info(e).is_cast())
                out() << "]";
            else if (!binding_info(e).is_contextual())
                out() << "]]";
            else
                out() << ")";
            e = p.first;
        }
        out() << ", ";
        print_child(e);
    }

    void print_const(expr const & a) {
        list<level> const & ls = const_levels(a);
        out() << const_name(a);
        if (!is_nil(ls)) {
            out() << ".{";
            bool first = true;
            for (auto l : ls) {
                if (first) first = false; else out() << " ";
                out() << l;
            }
            out() << "}";
        }
    }

    void print(expr const & a) {
        switch (a.kind()) {
        case expr_kind::Meta:
            out() << "?" << mlocal_name(a);
            break;
        case expr_kind::Local:
            out() << local_pp_name(a);
            break;
        case expr_kind::Var:
            out() << "#" << var_idx(a);
            break;
        case expr_kind::Constant:
            print_const(a);
            break;
        case expr_kind::App:
            print_app(a);
            break;
        case expr_kind::Lambda:
            print_binding("fun", a);
            break;
        case expr_kind::Pi:
            if (!is_arrow(a)) {
                print_binding("Pi", a);
            } else {
                print_child(binding_domain(a));
                out() << " -> ";
                print_arrow_body(lower_free_vars(binding_body(a), 1));
            }
            break;
        case expr_kind::Let:
            print_let(a);
            break;
        case expr_kind::Sort:
            print_sort(a);
            break;
        case expr_kind::Macro:
            print_macro(a);
            break;
        }
    }

    print_expr_fn(std::ostream & out, bool type0_as_bool = true):m_out(out), m_type0_as_bool(type0_as_bool) {}

    void operator()(expr const & e) {
        scoped_expr_caching set(false);
        print(e);
    }
};

std::ostream & operator<<(std::ostream & out, expr const & e) {
    print_expr_fn pr(out);
    pr(e);
    return out;
}

class simple_formatter_cell : public formatter_cell {
public:
    virtual format operator()(environment const & env, expr const & e, options const &) const {
        std::ostringstream s;
        print_expr_fn pr(s, env.prop_proof_irrel());
        pr(e);
        return format(s.str());
    }
};
formatter mk_simple_formatter() {
    return mk_formatter(simple_formatter_cell());
}
void print(lean::expr const & a) { std::cout << a << std::endl; }
}
