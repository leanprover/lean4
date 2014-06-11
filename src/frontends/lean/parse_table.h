/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/buffer.h"
#include "util/lua.h"
#include "kernel/expr.h"
#include "frontends/lean/token_table.h"

namespace lean {
class parser;
namespace notation {
typedef std::function<expr(parser &, unsigned, expr const *)> parse_fn;

enum class action_kind { Skip, Expr, Exprs, Binder, Binders, ScopedExpr, Ext };
struct action_cell;

/**
   \brief Action that must be performed after a token is consumed.
   The possible actions are:

   - Skip:    do nothing, just consume the token.
   - Expr:    parse a Lean expression using a given right-binding-power (rbp).
   - Exprs:   parse a sequence of expressions separated by a given token.
              The expressions are parsed using the given right-binding-power (rbp).
              The multiple expressions are combined into a single expression by folding them
              using an expression (rec) with two free variables and an initial element, fold left and right are supported.
   - Binder:  parse a single Lean binder.
   - Binders: parse a sequence of Lean binders.
   - ScopedExpr: parse an expression using the previous binder(s).
                 The resulting expression is computed using an expression (rec) with one free variable.
   - Ext:    invokes an external procedure parse_fn. This is used to define notation that does
              complicated notation.

    The parse_table datastructure applies "left factoring" when actions are "compatible".

    \remark Ext actions are never compatible with anything.
*/
class action {
    action_cell * m_ptr;
    explicit action(action_cell * ptr);
    static action g_skip_action;
    static action g_binder_action;
    static action g_binders_action;
public:
    action();
    action(action const & s);
    action(action && s);
    ~action();

    action & operator=(action const & s);
    action & operator=(action && s);

    friend action mk_skip_action();
    friend action mk_expr_action(unsigned rbp);
    friend action mk_exprs_action(name const & sep, expr const & rec, expr const & ini, bool right, unsigned rbp);
    friend action mk_binder_action();
    friend action mk_binders_action();
    friend action mk_scoped_expr_action(expr const & rec, unsigned rbp, bool lambda);
    friend action mk_ext_parse_action(parse_fn const & fn);

    action_kind kind() const;
    unsigned rbp() const;
    name const & get_sep() const;
    expr const & get_rec() const;
    expr const & get_initial() const;
    bool is_fold_right() const;
    bool use_lambda_abstraction() const;
    parse_fn const & get_parse_fn() const;

    bool is_compatible(action const & a) const;
};

action mk_skip_action();
action mk_expr_action(unsigned rbp = 0);
action mk_exprs_action(name const & sep, expr const & rec, expr const & ini, bool right, unsigned rbp = 0);
action mk_binder_action();
action mk_binders_action();
action mk_scoped_expr_action(expr const & rec, unsigned rbp = 0, bool lambda = true);
action mk_proc_action(parse_fn const & fn);

class transition {
    name           m_token;
    action         m_action;
public:
    transition(name const & t, action const & a):
        m_token(t), m_action(a) {}
    name const & get_token() const { return m_token; }
    action const & get_action() const { return m_action; }
};

/**
   \brief Parse table "transition rules" for implementing a Pratt's parser.
   The table supports "left factoring" in the methods \c add and \c merge.
*/
class parse_table {
    struct cell;
    cell * m_ptr;
    explicit parse_table(cell * c);
    parse_table add_core(unsigned num, transition const * ts, expr const & a, bool overload) const;
    void for_each(buffer<transition> & ts, std::function<void(unsigned, transition const *, list<expr> const &)> const & fn) const;
public:
    parse_table(bool nud = true);
    parse_table(parse_table const & s);
    parse_table(parse_table && s);
    ~parse_table();
    parse_table & operator=(parse_table const & n);
    parse_table & operator=(parse_table&& n);

    bool is_nud() const;
    parse_table add(unsigned num, transition const * ts, expr const & a, bool overload) const;
    parse_table merge(parse_table const & s, bool overload) const;
    optional<std::pair<action, parse_table>> find(name const & tk) const;
    list<expr> const & is_accepting() const;
    void for_each(std::function<void(unsigned, transition const *, list<expr> const &)> const & fn) const;
};
}
typedef notation::parse_table parse_table;
void open_parse_table(lua_State * L);
}
