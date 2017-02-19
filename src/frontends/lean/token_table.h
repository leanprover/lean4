/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <string>
#include "util/trie.h"
#include "util/name.h"

#ifndef LEAN_DEFAULT_PRECEDENCE
#define LEAN_DEFAULT_PRECEDENCE 1
#endif

namespace lean {
// User-level maximum precedence
unsigned get_max_prec();
// Internal maximum precedence used for @@ and @ operators
unsigned get_Max_prec();
unsigned get_arrow_prec();
class token_info {
    bool        m_command;
    name        m_token;
    name        m_value;
    unsigned    m_expr_precedence;
    unsigned    m_tactic_precedence;
    token_info(bool c, name const & t, name const & v, unsigned ep, unsigned tp):
        m_command(c), m_token(t), m_value(v), m_expr_precedence(ep), m_tactic_precedence(tp) {}
public:
    token_info():m_command(true) {}
    token_info(char const * val):
        m_command(true), m_token(val), m_value(val), m_expr_precedence(0), m_tactic_precedence(0) {}
    token_info(char const * token, char const * val):
        m_command(true), m_token(token), m_value(val), m_expr_precedence(0), m_tactic_precedence(0) {}
    token_info(char const * token, char const * val, unsigned prec, unsigned tac_prec):
        m_command(false), m_token(token), m_value(val),
        m_expr_precedence(prec), m_tactic_precedence(tac_prec) {}
    bool is_command() const { return m_command; }
    name const & token() const { return m_token; }
    name const & value() const { return m_value; }
    unsigned expr_precedence() const { return m_expr_precedence; }
    unsigned tactic_precedence() const { return m_tactic_precedence; }
    token_info update_expr_precedence(unsigned prec) const {
        return token_info(m_command, m_token, m_value, prec, m_tactic_precedence);
    }
    token_info update_tactic_precedence(unsigned prec) const {
        return token_info(m_command, m_token, m_value, m_expr_precedence, prec);
    }
};

typedef ctrie<token_info> token_table;
token_table mk_token_table();
token_table mk_default_token_table();
token_table add_command_token(token_table const & s, char const * token);
token_table add_command_token(token_table const & s, char const * token, char const * val);
token_table add_token(token_table const & s, char const * token, unsigned prec = LEAN_DEFAULT_PRECEDENCE);
token_table add_token(token_table const & s, char const * token, char const * val, unsigned prec = LEAN_DEFAULT_PRECEDENCE);
token_table add_tactic_token(token_table const & s, char const * token, unsigned prec = LEAN_DEFAULT_PRECEDENCE);
token_table add_tactic_token(token_table const & s, char const * token, char const * val, unsigned prec = LEAN_DEFAULT_PRECEDENCE);
void for_each(token_table const & s, std::function<void(char const *, token_info const&)> const & fn);
token_table const * find(token_table const & s, char c);
optional<unsigned> get_expr_precedence(token_table const & s, char const * token);
optional<unsigned> get_tactic_precedence(token_table const & s, char const * token);
bool is_token(token_table const & s, char const * token);
token_info const * value_of(token_table const & s);
void initialize_token_table();
void finalize_token_table();
}
