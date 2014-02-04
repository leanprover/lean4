/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/justification.h"
#include "kernel/expr.h"
#include "kernel/context.h"

namespace lean {
class metavar_env;
/**
   \brief Justification produced by the type checker when processing applications and pairs.
   Suppose \c m_expr is an application <tt>(f ...)</tt>, the type \c T of \c f contains metavariables, and
   it is not clear whether it is a Pi or not. In this case, the type checker adds
   the constraint

       <tt>ctx |- T == Pi (x : ?A), ?B</tt>

   where, \c ?A and \c ?B are fresh metavariables.
   This justification cell is used to justify the new constraint.

   Similarly, suppose \c m_expr is a projection <tt>(proj_i t)</tt>, and it is not clear whether
   type of \c t is a Sigma type because it contains metavariables. In this case, the type checker
   adds the constraints

      <tt>ctx |- T == Sigma (x : ?A), ?B</tt>
*/
class abstraction_expected_justification_cell : public justification_cell {
    context m_ctx;
    expr    m_expr;
    virtual char const * get_abst_str() const = 0;
public:
    abstraction_expected_justification_cell(context const & c, expr const & e):m_ctx(c), m_expr(e) {}
    virtual ~abstraction_expected_justification_cell();
    virtual format pp_header(formatter const & fmt, options const & opts, optional<metavar_env> const & menv) const;
    virtual void get_children(buffer<justification_cell*> &) const;
    virtual optional<expr> get_main_expr() const;
    context const & get_context() const { return m_ctx; }
    expr const & get_expr() const { return m_expr; }
};

class function_expected_justification_cell : public abstraction_expected_justification_cell {
    virtual char const * get_abst_str() const;
public:
    function_expected_justification_cell(context const & c, expr const & e):abstraction_expected_justification_cell(c, e) {}
};

class pair_expected_justification_cell : public abstraction_expected_justification_cell {
    virtual char const * get_abst_str() const;
public:
    pair_expected_justification_cell(context const & c, expr const & e):abstraction_expected_justification_cell(c, e) {}
};

/**
   \brief Justification produced by the type checker for application argument type matching.
   When checking an application <tt>(f a_1 ... a_i ...)</tt>, the type
   inferred for \c a_i must be convertible to the expected type.
   If the expected or inferred type contain metavariables, and it is not clear whether
   the inferred is convertible to expected, then the type checker adds the constraint

      <tt>ctx |- inferred << expected</tt>

   This justification cell is used to justify this constraint.
*/
class app_type_match_justification_cell : public justification_cell {
    context  m_ctx;
    expr     m_app;
    unsigned m_i;
public:
    app_type_match_justification_cell(context const & c, expr const & a, unsigned i):m_ctx(c), m_app(a), m_i(i) {}
    virtual ~app_type_match_justification_cell();
    virtual format pp_header(formatter const & fmt, options const & opts, optional<metavar_env> const & menv) const;
    virtual void get_children(buffer<justification_cell*> &) const;
    virtual optional<expr> get_main_expr() const;
    context const & get_context() const { return m_ctx; }
    expr const & get_app() const { return m_app; }
    unsigned get_arg_pos() const { return m_i; }
};

/**
   \brief Justification produced by the type checker for pairs.
   When checking a pair <tt>(pair f s t)</tt>, the type
   inferred for \c f (\c s) must be convertible to the expected type in the sigma type \c t.
   If the expected or inferred type contain metavariables, and it is not clear whether
   the inferred is convertible to expected, then the type checker adds the constraint

      <tt>ctx |- inferred << expected</tt>

   This justification cell is used to justify this constraint.
*/
class pair_type_match_justification_cell : public justification_cell {
    context  m_ctx;
    expr     m_expr;
    bool     m_first; // first/second component
public:
    pair_type_match_justification_cell(context const & c, expr const & a, bool f):m_ctx(c), m_expr(a), m_first(f) {}
    virtual ~pair_type_match_justification_cell();
    virtual format pp_header(formatter const & fmt, options const & opts, optional<metavar_env> const & menv) const;
    virtual void get_children(buffer<justification_cell*> &) const;
    virtual optional<expr> get_main_expr() const;
    context const & get_context() const { return m_ctx; }
    expr const & get_expr() const { return m_expr; }
    bool first() const { return m_first; }
};

/**
   \brief Justification produced by the type checker when the type \c T of \c type must be of the form
   <tt>Type l</tt>, and \c T constains metavariables, and it is not of this form.
   The type checker adds the following constraint

      <tt>ctx |- T << Type U+1</tt>

   This justification cell is used to justify these constraints.
*/
class type_expected_justification_cell : public justification_cell {
    context m_ctx;
    expr    m_type;
public:
    type_expected_justification_cell(context const & c, expr const & t):m_ctx(c), m_type(t) {}
    virtual ~type_expected_justification_cell();
    virtual format pp_header(formatter const & fmt, options const & opts, optional<metavar_env> const & menv) const;
    virtual void get_children(buffer<justification_cell*> &) const;
    virtual optional<expr> get_main_expr() const;
    context const & get_context() const { return m_ctx; }
    expr const & get_type() const { return m_type; }
};

/**
   \brief If \c type is of the form <tt>Pi x : A, B</tt>, where \c A has type \c T1 and \c B has type \c T2,
   and \c T1 or \c T2 have metavariables, then the type checker adds the following constraint

     <tt>ctx |- max(T1, T2) == ?T

   where ?T is a new metavariable, and this justification cell is used to justify the new constraint.
*/
class max_type_justification_cell : public type_expected_justification_cell {
public:
    max_type_justification_cell(context const & c, expr const & t):type_expected_justification_cell(c, t) {}
};

/**
   \brief Justification produced by the type checker when checking whether the type \c T_inferred of \c value
   is convertible to the expected type \c T_expected. If \c T_expected or \c T_inferred contain
   metavariables, and it is not clear whether \c T_inferred is convertible to \c T_expected,
   then the type checker adds the constraint

      <tt>ctx |- T_inferred << T_expected</tt>

   This justification cell is used to justify this constraint.
*/
class def_type_match_justification_cell : public justification_cell {
    context m_ctx;
    name    m_name;
    expr    m_value;
public:
    def_type_match_justification_cell(context const & c, name const & n, expr const & v):m_ctx(c), m_name(n), m_value(v) {}
    virtual ~def_type_match_justification_cell();
    virtual format pp_header(formatter const & fmt, options const & opts, optional<metavar_env> const & menv) const;
    virtual void get_children(buffer<justification_cell*> &) const;
    virtual optional<expr> get_main_expr() const;
    context const & get_context() const { return m_ctx; }
    name const & get_name() const { return m_name; }
    expr const & get_value() const { return m_value; }
};

/**
   \brief Similar to def_type_match_justification_cell. It is used to sign that type of \c m_value
   must be convertible to \c m_type at context \c m_ctx.
*/
class type_match_justification_cell : public justification_cell {
    context m_ctx;
    expr    m_type;
    expr    m_value;
public:
    type_match_justification_cell(context const & c, expr const & t, expr const & v):m_ctx(c), m_type(t), m_value(v) {}
    virtual ~type_match_justification_cell();
    virtual format pp_header(formatter const & fmt, options const & opts, optional<metavar_env> const & menv) const;
    virtual void get_children(buffer<justification_cell*> &) const;
    virtual optional<expr> get_main_expr() const;
    context const & get_context() const { return m_ctx; }
    expr const & get_type() const { return m_type; }
    expr const & get_value() const { return m_value; }
};

inline justification mk_function_expected_justification(context const & ctx, expr const & app) { return justification(new function_expected_justification_cell(ctx, app)); }
inline justification mk_pair_expected_justification(context const & ctx, expr const & app) { return justification(new pair_expected_justification_cell(ctx, app)); }
inline justification mk_app_type_match_justification(context const & ctx, expr const & app, unsigned i) { return justification(new app_type_match_justification_cell(ctx, app, i)); }
inline justification mk_pair_type_match_justification(context const & ctx, expr const & e, bool first) { return justification(new pair_type_match_justification_cell(ctx, e, first)); }
inline justification mk_type_expected_justification(context const & ctx, expr const & type) { return justification(new type_expected_justification_cell(ctx, type)); }
inline justification mk_max_type_justification(context const & ctx, expr const & type) { return justification(new max_type_justification_cell(ctx, type)); }
inline justification mk_def_type_match_justification(context const & ctx, name const & n, expr const & v) { return justification(new def_type_match_justification_cell(ctx, n, v)); }
inline justification mk_type_match_justification(context const & ctx, expr const & t, expr const & v) { return justification(new type_match_justification_cell(ctx, t, v)); }
}
