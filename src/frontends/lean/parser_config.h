/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/parse_table.h"
#include "frontends/lean/cmd_table.h"

namespace lean {
struct token_entry {
    std::string m_token;
    unsigned    m_prec;
    token_entry(std::string const & tk, unsigned prec):m_token(tk), m_prec(prec) {}
};

struct notation_entry {
    typedef notation::transition transition;
    bool             m_is_nud;
    list<transition> m_transitions;
    expr             m_expr;
    bool             m_overload;
    notation_entry():m_is_nud(true) {}
    notation_entry(bool is_nud, list<transition> const & ts, expr const & e, bool overload):
        m_is_nud(is_nud), m_transitions(ts), m_expr(e), m_overload(overload) {}
};

/** \brief Apply \c f to expressions embedded in the notation entry */
notation_entry replace(notation_entry const & e, std::function<expr(expr const &)> const & f);

environment add_token(environment const & env, token_entry const & e);
environment add_notation(environment const & env, notation_entry const & e);

environment add_token(environment const & env, char const * val, unsigned prec);
environment add_nud_notation(environment const & env, unsigned num, notation::transition const * ts, expr const & a, bool overload = true);
environment add_led_notation(environment const & env, unsigned num, notation::transition const * ts, expr const & a, bool overload = true);
environment add_nud_notation(environment const & env, std::initializer_list<notation::transition> const & ts, expr const & a,
                             bool overload = true);
environment add_led_notation(environment const & env, std::initializer_list<notation::transition> const & ts, expr const & a,
                             bool overload = true);
token_table const & get_token_table(environment const & env);
parse_table const & get_nud_table(environment const & env);
parse_table const & get_led_table(environment const & env);
cmd_table const & get_cmd_table(environment const & env);
/** \brief Force notation from namespace \c n to shadow any existing notation */
environment overwrite_notation(environment const & env, name const & n);
}
