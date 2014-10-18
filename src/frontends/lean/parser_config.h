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

enum class notation_entry_kind { NuD, LeD, Numeral };

class notation_entry {
    typedef notation::transition transition;
    notation_entry_kind  m_kind;
    union {
        list<transition> m_transitions;
        mpz              m_num;
    };
    expr                 m_expr;
    bool                 m_overload;
    bool                 m_safe_ascii;
public:
    notation_entry();
    notation_entry(notation_entry const & e);
    notation_entry(bool is_nud, list<transition> const & ts, expr const & e, bool overload);
    notation_entry(mpz const & val, expr const & e, bool overload);
    notation_entry(notation_entry const & e, bool overload);
    ~notation_entry();
    notation_entry_kind kind() const { return m_kind; }
    bool is_numeral() const { return m_kind == notation_entry_kind::Numeral; }
    bool is_nud() const { return m_kind == notation_entry_kind::NuD; }
    list<transition> const & get_transitions() const { lean_assert(!is_numeral()); return m_transitions; }
    mpz const & get_num() const { lean_assert(is_numeral()); return m_num; }
    expr const & get_expr() const { return m_expr; }
    bool overload() const { return m_overload; }
    bool is_safe_ascii() const { return m_safe_ascii; }
};
bool operator==(notation_entry const & e1, notation_entry const & e2);
inline bool operator!=(notation_entry const & e1, notation_entry const & e2) {
    return !(e1 == e2);
}

/** \brief Apply \c f to expressions embedded in the notation entry */
notation_entry replace(notation_entry const & e, std::function<expr(expr const &)> const & f);

environment add_token(environment const & env, token_entry const & e);
environment add_notation(environment const & env, notation_entry const & e);

environment add_token(environment const & env, char const * val, unsigned prec);
environment add_nud_notation(environment const & env, unsigned num, notation::transition const * ts, expr const & a,
                             bool overload = true);
environment add_led_notation(environment const & env, unsigned num, notation::transition const * ts, expr const & a,
                             bool overload = true);
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

/** \brief Add \c n as notation for \c e */
environment add_mpz_notation(environment const & env, mpz const & n, expr const & e, bool overload = true);
/** \brief Return the additional interpretations for \c n in the current environment.

    \remark It does not include the default one based on the \c num inductive datatype.
*/
list<expr> get_mpz_notation(environment const & env, mpz const & n);

/** \brief Return the notation declaration that start with a given head symbol.

    \remark Notation declarations that contain C++ and Lua actions are not indexed.
    Thus, they are to included in the result.
*/
list<notation_entry> get_notation_entries(environment const & env, head_index const & idx);

void initialize_parser_config();
void finalize_parser_config();
}
