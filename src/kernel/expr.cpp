/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#include <vector>
#include <sstream>
#include "util/hash.h"
#include "kernel/expr.h"
#include "kernel/free_vars.h"
#include "kernel/expr_eq.h"
#include "kernel/metavar.h"

namespace lean {
local_entry::local_entry(unsigned s, unsigned n):m_kind(local_entry_kind::Lift), m_s(s), m_n(n) {}
local_entry::local_entry(unsigned s, expr const & v):m_kind(local_entry_kind::Inst), m_s(s), m_v(v) {}
local_entry::~local_entry() {}
bool local_entry::operator==(local_entry const & e) const {
    if (m_kind != e.m_kind || m_s != e.m_s)
        return false;
    if (is_inst())
        return m_v == e.m_v;
    else
        return m_n == e.m_n;
}

unsigned hash_args(unsigned size, expr const * args) {
    return hash(size, [&args](unsigned i){ return args[i].hash(); });
}

static expr g_null;

expr const & expr::null() {
    lean_assert(!g_null);
    return g_null;
}

expr_cell::expr_cell(expr_kind k, unsigned h, bool has_mv):
    m_kind(static_cast<unsigned>(k)),
    m_flags(has_mv ? 4 : 0),
    m_hash(h),
    m_rc(1) {
    // m_hash_alloc does not need to be a unique identifier.
    // We want diverse hash codes such that given expr_cell * c1 and expr_cell * c2,
    // if c1 != c2, then there is high probability c1->m_hash_alloc != c2->m_hash_alloc.
    // Remark: using pointer address as a hash code is not a good idea.
    //    - each execution run will behave differently.
    //    - the hash is not diverse enough
    static thread_local unsigned g_hash_alloc_counter = 0;
    m_hash_alloc = g_hash_alloc_counter;
    g_hash_alloc_counter++;
}

expr_var::expr_var(unsigned idx):
    expr_cell(expr_kind::Var, idx, false),
    m_vidx(idx) {}

expr_const::expr_const(name const & n):
    expr_cell(expr_kind::Constant, n.hash(), false),
    m_name(n) {}

expr_app::expr_app(unsigned num_args, bool has_mv):
    expr_cell(expr_kind::App, 0, has_mv),
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
    bool has_mv = std::any_of(as, as + n, [](expr const & c) { return c.has_metavar(); });
    // Remark: we represent ((app a b) c) as (app a b c)
    if (is_app(arg0)) {
        n0    = num_args(arg0);
        new_n = n + n0 - 1;
    } else {
        new_n = n;
    }
    char * mem   = new char[sizeof(expr_app) + new_n*sizeof(expr)];
    expr r(new (mem) expr_app(new_n, has_mv));
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
    expr_cell(expr_kind::Eq, ::lean::hash(lhs.hash(), rhs.hash()), lhs.has_metavar() || rhs.has_metavar()),
    m_lhs(lhs),
    m_rhs(rhs) {
}
expr_eq::~expr_eq() {}
expr_abstraction::expr_abstraction(expr_kind k, name const & n, expr const & t, expr const & b):
    expr_cell(k, ::lean::hash(t.hash(), b.hash()), t.has_metavar() || b.has_metavar()),
    m_name(n),
    m_domain(t),
    m_body(b) {
}
expr_lambda::expr_lambda(name const & n, expr const & t, expr const & e):expr_abstraction(expr_kind::Lambda, n, t, e) {}
expr_pi::expr_pi(name const & n, expr const & t, expr const & e):expr_abstraction(expr_kind::Pi, n, t, e) {}
expr_type::expr_type(level const & l):
    expr_cell(expr_kind::Type, l.hash(), false),
    m_level(l) {
}
expr_type::~expr_type() {}
expr_let::expr_let(name const & n, expr const & t, expr const & v, expr const & b):
    expr_cell(expr_kind::Let, ::lean::hash(v.hash(), b.hash()), v.has_metavar() || b.has_metavar() || (t && t.has_metavar())),
    m_name(n),
    m_type(t),
    m_value(v),
    m_body(b) {
}
expr_let::~expr_let() {}
name value::get_unicode_name() const { return get_name(); }
bool value::normalize(unsigned, expr const *, expr &) const { return false; }
void value::display(std::ostream & out) const { out << get_name(); }
bool value::operator==(value const & other) const { return typeid(*this) == typeid(other); }
bool value::operator<(value const & other) const {
    if (get_name() == other.get_name())
        return lt(other);
    else
        return get_name() < other.get_name();
}
format value::pp() const { return format(get_name()); }
format value::pp(bool unicode, bool) const { return unicode ? format(get_unicode_name()) : pp(); }
unsigned value::hash() const { return get_name().hash(); }
expr_value::expr_value(value & v):
    expr_cell(expr_kind::Value, v.hash(), false),
    m_val(v) {
    m_val.inc_ref();
}
expr_value::~expr_value() {
    m_val.dec_ref();
}
expr_metavar::expr_metavar(name const & n, local_context const & lctx):
    expr_cell(expr_kind::MetaVar, n.hash(), true),
    m_name(n), m_lctx(lctx) {}
expr_metavar::~expr_metavar() {}

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
    case expr_kind::MetaVar:    delete static_cast<expr_metavar*>(this); break;
    }
}

expr mk_type() {
    static thread_local expr r = mk_type(level());
    return r;
}

bool operator==(expr const & a, expr const & b) {
    return expr_eq_fn<>()(a, b);
}

bool is_arrow(expr const & t) {
    return is_pi(t) && !has_free_var(abst_body(t), 0);
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
    case expr_kind::Let:      return mk_let(let_name(a), let_type(a), let_value(a), let_body(a));
    case expr_kind::MetaVar:  return mk_metavar(metavar_name(a), metavar_lctx(a));
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}
}
