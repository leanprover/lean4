/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#include <vector>
#include <sstream>
#include "expr.h"
#include "free_vars.h"
#include "sets.h"
#include "hash.h"
#include "format.h"

namespace lean {

unsigned hash_args(unsigned size, expr const * args) {
    return hash(size, [&args](unsigned i){ return args[i].hash(); });
}

expr_cell::expr_cell(expr_kind k, unsigned h):
    m_kind(static_cast<unsigned>(k)),
    m_flags(0),
    m_hash(h),
    m_rc(1) {}

expr_var::expr_var(unsigned idx):
    expr_cell(expr_kind::Var, idx),
    m_vidx(idx) {}

expr_const::expr_const(name const & n):
    expr_cell(expr_kind::Constant, n.hash()),
    m_name(n) {}

expr_app::expr_app(unsigned num_args):
    expr_cell(expr_kind::App, 0),
    m_num_args(num_args) {
}
expr_app::~expr_app() {
    for (unsigned i = 0; i < m_num_args; i++)
        (m_args+i)->~expr();
}
expr mk_app(unsigned n, expr const * as) {
    lean_assert(n > 1);
    unsigned new_n;
    unsigned n0 = 0;
    expr const & arg0 = as[0];
    // Remark: we represent ((app a b) c) as (app a b c)
    if (is_app(arg0)) {
        n0    = num_args(arg0);
        new_n = n + n0 - 1;
    }
    else {
        new_n = n;
    }
    char * mem   = new char[sizeof(expr_app) + new_n*sizeof(expr)];
    expr r(new (mem) expr_app(new_n));
    expr * m_args = to_app(r)->m_args;
    unsigned i = 0;
    unsigned j = 0;
    if (new_n != n) {
        for (; i < n0; i++)
            new (m_args+i) expr(arg(arg0, i));
        j++;
    }
    for (; i < new_n; ++i, ++j) {
        lean_assert(j < n);
        new (m_args+i) expr(as[j]);
    }
    to_app(r)->m_hash = hash_args(new_n, m_args);
    return r;
}
expr_eq::expr_eq(expr const & lhs, expr const & rhs):
    expr_cell(expr_kind::Eq, ::lean::hash(lhs.hash(), rhs.hash())),
    m_lhs(lhs),
    m_rhs(rhs) {
}
expr_eq::~expr_eq() {
}
expr_abstraction::expr_abstraction(expr_kind k, name const & n, expr const & t, expr const & b):
    expr_cell(k, ::lean::hash(t.hash(), b.hash())),
    m_name(n),
    m_domain(t),
    m_body(b) {
}
expr_lambda::expr_lambda(name const & n, expr const & t, expr const & e):
    expr_abstraction(expr_kind::Lambda, n, t, e) {}
expr_pi::expr_pi(name const & n, expr const & t, expr const & e):
    expr_abstraction(expr_kind::Pi, n, t, e) {}

expr_type::expr_type(level const & l):
    expr_cell(expr_kind::Type, l.hash()),
    m_level(l) {
}
expr_type::~expr_type() {
}
expr_let::expr_let(name const & n, expr const & v, expr const & b):
    expr_cell(expr_kind::Let, ::lean::hash(v.hash(), b.hash())),
    m_name(n),
    m_value(v),
    m_body(b) {
}
expr_let::~expr_let() {
}
expr_value::expr_value(value & v):
    expr_cell(expr_kind::Value, v.hash()),
    m_val(v) {
    m_val.inc_ref();
}
expr_value::~expr_value() {
    m_val.dec_ref();
}

void expr_cell::dealloc() {
    switch (kind()) {
    case expr_kind::Var:        delete static_cast<expr_var*>(this); break;
    case expr_kind::Constant:   delete static_cast<expr_const*>(this); break;
    case expr_kind::App:        static_cast<expr_app*>(this)->~expr_app(); delete[] reinterpret_cast<char*>(this); break;
    case expr_kind::Eq:         delete static_cast<expr_eq*>(this); break;
    case expr_kind::Lambda:     delete static_cast<expr_lambda*>(this); break;
    case expr_kind::Pi:         delete static_cast<expr_pi*>(this); break;
    case expr_kind::Type:       delete static_cast<expr_type*>(this); break;
    case expr_kind::Value:      delete static_cast<expr_value*>(this); break;
    case expr_kind::Let:        delete static_cast<expr_let*>(this); break;
    }
}

expr mk_type() {
    static thread_local expr r = mk_type(level());
    return r;
}

class eq_fn {
    expr_cell_pair_set m_eq_visited;

    bool apply(expr const & a, expr const & b) {
        if (is_eqp(a, b))         return true;
        if (a.hash() != b.hash()) return false;
        if (a.kind() != b.kind()) return false;
        if (is_var(a))            return var_idx(a) == var_idx(b);
        if (is_shared(a) && is_shared(b)) {
            auto p = std::make_pair(a.raw(), b.raw());
            if (m_eq_visited.find(p) != m_eq_visited.end())
                return true;
            m_eq_visited.insert(p);
        }
        switch (a.kind()) {
        case expr_kind::Var:      lean_unreachable(); return true;
        case expr_kind::Constant: return const_name(a) == const_name(b);
        case expr_kind::App:
            if (num_args(a) != num_args(b))
                return false;
            for (unsigned i = 0; i < num_args(a); i++)
                if (!apply(arg(a, i), arg(b, i)))
                    return false;
            return true;
        case expr_kind::Eq:       return apply(eq_lhs(a), eq_lhs(b)) && apply(eq_rhs(a), eq_rhs(b));
        case expr_kind::Lambda:
        case expr_kind::Pi:
            // Lambda and Pi
            // Remark: we ignore get_abs_name because we want alpha-equivalence
            return apply(abst_domain(a), abst_domain(b)) && apply(abst_body(a), abst_body(b));
        case expr_kind::Type:     return ty_level(a) == ty_level(b);
        case expr_kind::Value:    return to_value(a) == to_value(b);
        case expr_kind::Let:      return apply(let_value(a), let_value(b)) && apply(let_body(a), let_body(b));
        }
        lean_unreachable();
        return false;
    }
public:
    bool operator()(expr const & a, expr const & b) {
        return apply(a, b);
    }
};

bool operator==(expr const & a, expr const & b) {
    return eq_fn()(a, b);
}

bool is_arrow(expr const & t) {
    return is_pi(t) && !has_free_var(abst_body(t), 0);
}

// Low-level pretty printer
std::ostream & operator<<(std::ostream & out, expr const & a) {
    switch (a.kind()) {
    case expr_kind::Var:      out << "#" << var_idx(a); break;
    case expr_kind::Constant: out << const_name(a);     break;
    case expr_kind::App:
        out << "(";
        for (unsigned i = 0; i < num_args(a); i++) {
            if (i > 0) out << " ";
            out << arg(a, i);
        }
        out << ")";
        break;
    case expr_kind::Eq:      out << "(" << eq_lhs(a) << " = " << eq_rhs(a) << ")"; break;
    case expr_kind::Lambda:  out << "(fun " << abst_name(a) << " : " << abst_domain(a) << " => " << abst_body(a) << ")"; break;
    case expr_kind::Pi:
        if (!is_arrow(a))
            out << "(pi " << abst_name(a) << " : " << abst_domain(a) << ", " << abst_body(a) << ")";
        else if (!is_arrow(abst_domain(a)))
            out << abst_domain(a) << " -> " << abst_body(a);
        else
            out << "(" << abst_domain(a) << ") -> " << abst_body(a);
        break;
    case expr_kind::Let:  out << "(let " << let_name(a) << " := " << let_value(a) << " in " << let_body(a) << ")"; break;
    case expr_kind::Type: {
        level const & l = ty_level(a);
        if (l == level())
            out << "Type";
        else
            out << "(Type " << ty_level(a) << ")";
        break;
    }
    case expr_kind::Value: to_value(a).display(out); break;
    }
    return out;
}

expr copy(expr const & a) {
    switch (a.kind()) {
    case expr_kind::Var:      return mk_var(var_idx(a));
    case expr_kind::Constant: return mk_constant(const_name(a));
    case expr_kind::Type:     return mk_type(ty_level(a));
    case expr_kind::Value:    return mk_value(static_cast<expr_value*>(a.raw())->m_val);
    case expr_kind::App:      return mk_app(num_args(a), begin_args(a));
    case expr_kind::Eq:       return mk_eq(eq_lhs(a), eq_rhs(a));
    case expr_kind::Lambda:   return mk_lambda(abst_name(a), abst_domain(a), abst_body(a));
    case expr_kind::Pi:       return mk_pi(abst_name(a), abst_domain(a), abst_body(a));
    case expr_kind::Let:      return mk_let(let_name(a), let_value(a), let_body(a));
    }
    lean_unreachable();
    return expr();
}
}

lean::format pp_aux(lean::expr const & a) {
    using namespace lean;
    switch (a.kind()) {
    case expr_kind::Var:
        return format{format("#"), format(static_cast<int>(var_idx(a)))};
    case expr_kind::Constant:
        return format(const_name(a));
    case expr_kind::Value:
        return to_value(a).pp();
    case expr_kind::App:
    {
        format r;
        for (unsigned i = 0; i < num_args(a); i++) {
            if (i > 0) r += format(" ");
            r += pp_aux(arg(a, i));
        }
        return paren(r);
    }
    case expr_kind::Eq:
        return paren(format{pp_aux(eq_lhs(a)), format("="), pp_aux(eq_rhs(a))});
    case expr_kind::Let:
        return paren(format{
                       highlight(format("let "), format::format_color::PINK), /* Use unicode lambda */
                       paren(format{
                               format(let_name(a)),
                               format(" := "),
                               pp_aux(let_value(a))}),
                       format(" in "),
                       pp_aux(let_body(a))});
    case expr_kind::Lambda:
        return paren(format{
                       highlight(format("\u03BB "), format::format_color::PINK), /* Use unicode lambda */
                       paren(format{
                               format(abst_name(a)),
                               format(" : "),
                               pp_aux(abst_domain(a))}),
                       format(" "),
                       pp_aux(abst_body(a))});
    case expr_kind::Pi:
        return paren(format{
                       highlight(format("\u03A0 "), format::format_color::ORANGE), /* Use unicode lambda */
                       paren(format{
                               format(abst_name(a)),
                               format(" : "),
                               pp_aux(abst_domain(a))}),
                       format(" "),
                       pp_aux(abst_body(a))});
    case expr_kind::Type:
    {
        std::stringstream ss;
        ss << ty_level(a);

        return paren(format{format("Type "),
                            format(ss.str())});
    }
    }
    lean_unreachable();
    return format();
}

void pp(lean::expr const & a) {
    lean::format const & f = pp_aux(a);
    std::cout << f;
}
