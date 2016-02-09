/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <utility>
#include "util/buffer.h"
#include "kernel/expr.h"
#include "library/head_map.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/parser_pos_provider.h"

#ifndef LEAN_DEFAULT_NOTATION_PRIORITY
#define LEAN_DEFAULT_NOTATION_PRIORITY 1000
#endif

namespace lean {
class parser;
class io_state_stream;
namespace notation {
typedef std::function<expr(parser &, unsigned, expr const *, pos_info const &)> parse_fn;

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

    friend void initialize_parse_table();
    friend action mk_expr_action(unsigned rbp);
    friend action mk_binders_action(unsigned rbp);
    friend action mk_binder_action(unsigned rbp);
    friend action mk_exprs_action(name const & sep, expr const & rec, optional<expr> const & ini,
                                  optional<name> const & terminator, bool right, unsigned rbp);
    friend action mk_scoped_expr_action(expr const & rec, unsigned rbp, bool lambda);
    friend action mk_ext_action_core(parse_fn const & fn);
    friend action mk_ext_action(parse_fn const & fn);

    action_kind kind() const;
    unsigned rbp() const;
    name const & get_sep() const;
    expr const & get_rec() const;
    optional<expr> const & get_initial() const;
    optional<name> const & get_terminator() const;
    bool is_fold_right() const;
    bool use_lambda_abstraction() const;
    parse_fn const & get_parse_fn() const;

    bool is_equal(action const & a) const;
    bool is_equivalent(action const & a) const;
    // We say two actions are compatible if the parser can decide which one to choose by looking at the next token.
    bool is_compatible(action const & a) const;

    void display(io_state_stream & out) const;

    /** \brief Return true iff the action is not Ext */
    bool is_simple() const;
};
inline bool operator==(action const & a1, action const & a2) { return a1.is_equal(a2); }
inline bool operator!=(action const & a1, action const & a2) { return !a1.is_equal(a2); }

action mk_skip_action();
action mk_expr_action(unsigned rbp = 0);
action mk_exprs_action(name const & sep, expr const & rec, optional<expr> const & ini, optional<name> const & terminator, bool right,
                       unsigned rbp = 0);
action mk_binder_action(unsigned rbp = 0);
action mk_binders_action(unsigned rbp = 0);
action mk_scoped_expr_action(expr const & rec, unsigned rbp = 0, bool lambda = true);
action mk_ext_action_core(parse_fn const & fn);
action mk_ext_action(parse_fn const & fn);

/** \brief Apply \c f to expressions embedded in the given action */
action replace(action const & a, std::function<expr(expr const &)> const & f);

class transition {
    name           m_token;
    name           m_pp_token;
    action         m_action;
public:
    transition(name const & t, action const & a, name pp_token = name::anonymous()):
        m_token(t), m_pp_token(pp_token ? pp_token : t), m_action(a) {}
    name const & get_token() const { return m_token; }
    name const & get_pp_token() const { return m_pp_token; }
    action const & get_action() const { return m_action; }
    bool is_simple() const { return m_action.is_simple(); }
    bool is_safe_ascii() const { return m_token.is_safe_ascii(); }
};
inline bool operator==(transition const & t1, transition const & t2) {
    return t1.get_token() == t2.get_token() && t1.get_action() == t2.get_action();
}
inline bool operator!=(transition const & t1, transition const & t2) {
    return !(t1 == t2);
}

/** \brief Apply \c f to expressions embedded in the given transition */
transition replace(transition const & t, std::function<expr(expr const &)> const & f);

class accepting {
    unsigned     m_prio;
    list<action> m_postponed; // exprs and scoped_expr actions
    expr         m_expr;      // resulting expression
public:
    accepting(unsigned prio, list<action> const & post, expr const & e):
        m_prio(prio), m_postponed(post), m_expr(e) {}
    unsigned get_prio() const { return m_prio; }
    list<action> const & get_postponed() const { return m_postponed; }
    expr const & get_expr() const { return m_expr; }
};

void display(io_state_stream & out, unsigned num, transition const * ts, list<accepting> const & es, bool nud,
             optional<token_table> const & tt);

/**
   \brief Parse table "transition rules" for implementing a Pratt's parser.
   The table supports "left factoring" in the methods \c add and \c merge.
*/
class parse_table {
    struct cell;
    cell * m_ptr;
    explicit parse_table(cell * c);
    parse_table add_core(unsigned num, transition const * ts, expr const & a, unsigned priority, bool overload, buffer<action> & postponed) const;
    void for_each(buffer<transition> & ts, std::function<void(unsigned, transition const *,
                                                              list<accepting> const &)> const & fn) const;
public:
    parse_table(bool nud = true);
    parse_table(parse_table const & s);
    parse_table(parse_table && s);
    ~parse_table();
    parse_table & operator=(parse_table const & n);
    parse_table & operator=(parse_table&& n);

    bool is_nud() const;
    parse_table add(unsigned num, transition const * ts, expr const & a, unsigned priority, bool overload) const;
    parse_table add(std::initializer_list<transition> const & ts, expr const & a) const {
        return add(ts.size(), ts.begin(), a, LEAN_DEFAULT_NOTATION_PRIORITY, true);
    }
    parse_table merge(parse_table const & s, bool overload) const;\
    list<pair<transition, parse_table>> find(name const & tk) const;
    list<accepting> const & is_accepting() const;
    void for_each(std::function<void(unsigned, transition const *, list<accepting> const &)> const & fn) const;

    void display(io_state_stream & out, optional<token_table> const & tk) const;
};

/** \brief Given a notation definition, return the "head symbol" of
    every instance of the given notation.

    \remark The result is none if the notation uses actions implemented in C++.
    The result is none if the denotation is a variable.
*/
optional<head_index> get_head_index(unsigned num, transition const * ts, expr const & a);

void initialize_parse_table();
void finalize_parse_table();
}
typedef notation::parse_table parse_table;
inline void initialize_parse_table() { notation::initialize_parse_table(); }
inline void finalize_parse_table() { notation::finalize_parse_table(); }
}
