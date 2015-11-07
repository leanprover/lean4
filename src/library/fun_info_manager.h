/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/expr_lt.h"
#include "library/type_context.h"

namespace lean {
class param_info {
    unsigned       m_implicit:1;
    unsigned       m_inst_implicit:1;
    unsigned       m_prop:1;
    unsigned       m_subsingleton:1;
    unsigned       m_is_dep:1; // true if rest depends on this parameter
    list<unsigned> m_deps; // previous arguments it depends on
public:
    param_info(bool imp, bool inst_imp, bool prop, bool sub, bool is_dep, list<unsigned> const & deps):
        m_implicit(imp), m_inst_implicit(inst_imp), m_prop(prop), m_subsingleton(sub),
        m_is_dep(is_dep), m_deps(deps) {}
    list<unsigned> const & get_dependencies() const { return m_deps; }
    bool is_prop() const { return m_prop; }
    bool is_implicit() const { return m_implicit; }
    bool is_inst_implicit() const { return m_inst_implicit; }
    bool is_subsingleton() const { return m_subsingleton; }
    bool is_dep() const { return m_is_dep; }
};

class fun_info {
    unsigned         m_arity;
    list<param_info> m_params_info;
    list<unsigned>   m_deps;
public:
    fun_info():m_arity(0) {}
    fun_info(unsigned arity, list<param_info> const & info, list<unsigned> const & deps):
        m_arity(arity), m_params_info(info), m_deps(deps) {}
    unsigned get_arity() const { return m_arity; }
    list<param_info> const & get_params_info() const { return m_params_info; }
    list<unsigned> const & get_dependencies() const { return m_deps; }
};

class fun_info_manager {
    type_context &                         m_ctx;
    rb_map<expr, fun_info, expr_quick_cmp> m_fun_info;
    list<unsigned> collect_deps(expr const & e, buffer<expr> const & locals);
public:
    fun_info_manager(type_context & ctx);
    type_context & ctx() { return m_ctx; }
    fun_info get(expr const & e);
};


/** \brief Given a term \c e of the form F[ts[0], ..., ts[n-1]],
    return F[rs[0], ..., rs[n-1]] only if the replacement does not produce type errors.

    Note that even if each ts[i] and rs[i] have the same type, the result may be none.

    Here is a very simple example:
    Given (f : Pi (n : nat), bv n -> bv n) (v : bv 10), then (F[v] := f 10 v) is type
    correct, but (f 11 v) is not.

    If
      a) F[ts[0], ..., ts[n-1] is type correct, and
      b) If there is a telescope T s.t. (ts[0], ..., ts[n-1]) and (rs[0], ..., rs[n-1]) are instances of T, and
      c) the result is not none
    Then
      the result is type correct.

    TODO(Leo): move to a different file?
*/
optional<expr> replace(fun_info_manager & infom, expr const & e, unsigned n, expr const * ts, expr const * rs);
inline optional<expr> replace(fun_info_manager & infom, expr const & e, buffer<expr> const & ts, buffer<expr> const & rs) {
    lean_assert(ts.size() == rs.size());
    return replace(infom, e, ts.size(), ts.data(), rs.data());
}
}
