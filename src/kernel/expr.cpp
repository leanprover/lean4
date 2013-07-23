/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "expr.h"
#include "expr_set.h"
#include "hash.h"

namespace lean {

unsigned hash_args(unsigned size, expr const * args) {
    return hash(size, [&args](unsigned i){ return args[i].hash(); });
}

unsigned hash_vars(unsigned size, uvar const * vars) {
    return hash(size, [&vars](unsigned i){ return vars[i].second.hash(); });
}

expr_cell::expr_cell(expr_kind k, unsigned h):
    m_kind(static_cast<unsigned>(k)),
    m_max_shared(0),
    m_hash(h),
    m_rc(1) {}

expr_var::expr_var(unsigned idx):
    expr_cell(expr_kind::Var, idx),
    m_vidx(idx) {}

expr_const::expr_const(name const & n, unsigned pos):
    expr_cell(expr_kind::Constant, n.hash()),
    m_name(n),
    m_pos(pos) {}

expr_app::expr_app(unsigned num_args):
    expr_cell(expr_kind::App, 0),
    m_num_args(num_args) {
}
expr_app::~expr_app() {
    for (unsigned i = 0; i < m_num_args; i++)
        (m_args+i)->~expr();
}
expr app(unsigned num_args, expr const * args) {
    lean_assert(num_args > 1);
    unsigned _num_args;
    unsigned _num_args0 = 0;
    expr const & arg0 = args[0];
    // Remark: we represet ((app a b) c) as (app a b c)
    if (is_app(arg0)) {
        _num_args0 = get_num_args(arg0);
        _num_args  = num_args + _num_args0 - 1;
    }
    else {
        _num_args = num_args;
    }
    char * mem   = new char[sizeof(expr_app) + _num_args*sizeof(expr)];
    expr r(new (mem) expr_app(_num_args));
    expr * m_args = to_app(r)->m_args;
    unsigned i = 0;
    unsigned j = 0;
    if (_num_args != num_args) {
        for (; i < _num_args0; i++)
            new (m_args+i) expr(get_arg(arg0, i));
        j++;
    }
    for (; i < _num_args; ++i, ++j) {
        lean_assert(j < num_args);
        new (m_args+i) expr(args[j]);
    }
    to_app(r)->m_hash = hash_args(_num_args, m_args);
    return r;
}

expr_abstraction::expr_abstraction(expr_kind k, name const & n, expr const & t, expr const & e):
    expr_cell(k, ::lean::hash(t.hash(), e.hash())),
    m_name(n),
    m_type(t),
    m_expr(e) {
}
expr_lambda::expr_lambda(name const & n, expr const & t, expr const & e):
    expr_abstraction(expr_kind::Lambda, n, t, e) {}
expr_pi::expr_pi(name const & n, expr const & t, expr const & e):
    expr_abstraction(expr_kind::Pi, n, t, e) {}

expr_type::expr_type(unsigned size, uvar const * vars):
    expr_cell(expr_kind::Type, hash_vars(size, vars)),
    m_size(size) {
    for (unsigned i = 0; i < m_size; i++)
        new (m_vars + i) uvar(vars[i]);
}
expr_type::~expr_type() {
    for (unsigned i = 0; i < m_size; i++)
        (m_vars+i)->~uvar();
}
expr type(unsigned size, uvar const * vars) {
    char * mem = new char[sizeof(expr_type) + size*sizeof(uvar)];
    return expr(new (mem) expr_type(size, vars));
}

expr_numeral::expr_numeral(mpz const & n):
    expr_cell(expr_kind::Numeral, n.hash()),
    m_numeral(n) {}

void expr_cell::dealloc() {
    switch (kind()) {
    case expr_kind::Var:        delete static_cast<expr_var*>(this); break;
    case expr_kind::Constant:   delete static_cast<expr_const*>(this); break;
    case expr_kind::App:        static_cast<expr_app*>(this)->~expr_app(); delete[] reinterpret_cast<char*>(this); break;
    case expr_kind::Lambda:     delete static_cast<expr_lambda*>(this); break;
    case expr_kind::Pi:         delete static_cast<expr_pi*>(this); break;
    case expr_kind::Prop:       delete static_cast<expr_prop*>(this); break;
    case expr_kind::Type:       static_cast<expr_type*>(this)->~expr_type(); delete[] reinterpret_cast<char*>(this); break;
    case expr_kind::Numeral:    delete static_cast<expr_numeral*>(this); break;
    }
}

namespace expr_eq_ns {
static thread_local expr_cell_pair_set g_eq_visited;
bool apply(expr const & a, expr const & b) {
    if (eqp(a, b))            return true;
    if (a.hash() != b.hash()) return false;
    if (a.kind() != b.kind()) return false;
    if (is_var(a))            return get_var_idx(a) == get_var_idx(b);
    if (is_prop(a))           return true;
    if (is_shared(a) && is_shared(b)) {
        auto p = std::make_pair(a.raw(), b.raw());
        if (g_eq_visited.find(p) != g_eq_visited.end())
            return true;
        g_eq_visited.insert(p);
    }
    switch (a.kind()) {
    case expr_kind::Var:      lean_unreachable(); return true;
    case expr_kind::Constant: return get_const_name(a) == get_const_name(b);
    case expr_kind::App:
        if (get_num_args(a) != get_num_args(b))
            return false;
        for (unsigned i = 0; i < get_num_args(a); i++)
            if (!apply(get_arg(a, i), get_arg(b, i)))
                return false;
        return true;
    case expr_kind::Lambda:
    case expr_kind::Pi:
        // Lambda and Pi
        // Remark: we ignore get_abs_name because we want alpha-equivalence
        return apply(get_abs_type(a), get_abs_type(b)) && apply(get_abs_expr(a), get_abs_expr(b));
    case expr_kind::Prop:     lean_unreachable(); return true;
    case expr_kind::Type:
        if (get_ty_num_vars(a) != get_ty_num_vars(b))
            return false;
        for (unsigned i = 0; i < get_ty_num_vars(a); i++) {
            uvar v1 = get_ty_var(a, i);
            uvar v2 = get_ty_var(b, i);
            if (v1.first != v2.first || v1.second != v2.second)
                return false;
        }
        return true;
    case expr_kind::Numeral:  return get_numeral(a) == get_numeral(b);
    }
    lean_unreachable();
    return false;
}
} // namespace expr_eq
bool operator==(expr const & a, expr const & b) {
    expr_eq_ns::g_eq_visited.clear();
    return expr_eq_ns::apply(a, b);
}

// Low-level pretty printer
std::ostream & operator<<(std::ostream & out, expr const & a) {
    switch (a.kind()) {
    case expr_kind::Var:      out << "#" << get_var_idx(a); break;
    case expr_kind::Constant: out << get_const_name(a);     break;
    case expr_kind::App:
        out << "(";
        for (unsigned i = 0; i < get_num_args(a); i++) {
            if (i > 0) out << " ";
            out << get_arg(a, i);
        }
        out << ")";
        break;
    case expr_kind::Lambda:  out << "(fun (" << get_abs_name(a) << " : " << get_abs_type(a) << ") " << get_abs_expr(a) << ")";    break;
    case expr_kind::Pi:      out << "(forall (" << get_abs_name(a) << " : " << get_abs_type(a) << ") " << get_abs_expr(a) << ")"; break;
    case expr_kind::Prop:    out << "Prop"; break;
    case expr_kind::Type:    out << "Type"; break;
    case expr_kind::Numeral: out << get_numeral(a); break;
    }
    return out;
}

}
