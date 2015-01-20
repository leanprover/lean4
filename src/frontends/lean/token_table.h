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
#include "util/lua.h"

#ifndef LEAN_DEFAULT_PRECEDENCE
#define LEAN_DEFAULT_PRECEDENCE 1
#endif

namespace lean {
// User-level maximum precedence
unsigned get_max_prec();
// Internal maximum precedence used for @ and ! operators
unsigned get_Max_prec();
unsigned get_arrow_prec();
unsigned get_decreasing_prec();
class token_info {
    bool        m_command;
    name        m_token;
    name        m_value;
    unsigned    m_precedence;
public:
    token_info():m_command(true) {}
    token_info(char const * val):
        m_command(true), m_token(val), m_value(val), m_precedence(LEAN_DEFAULT_PRECEDENCE) {}
    token_info(char const * token, char const * val):
        m_command(true), m_token(token), m_value(val), m_precedence(LEAN_DEFAULT_PRECEDENCE) {}
    token_info(char const * val, unsigned prec):
        m_command(false), m_token(val), m_value(val), m_precedence(prec) {}
    token_info(char const * token, char const * val, unsigned prec):
        m_command(false), m_token(token), m_value(val), m_precedence(prec) {}
    bool is_command() const { return m_command; }
    name const & token() const { return m_token; }
    name const & value() const { return m_value; }
    unsigned precedence() const { return m_precedence; }
};

typedef ctrie<token_info> token_table;
token_table mk_token_table();
token_table mk_default_token_table();
token_table add_command_token(token_table const & s, char const * token);
token_table add_command_token(token_table const & s, char const * token, char const * val);
token_table add_token(token_table const & s, char const * token, unsigned prec = LEAN_DEFAULT_PRECEDENCE);
token_table add_token(token_table const & s, char const * token, char const * val, unsigned prec = LEAN_DEFAULT_PRECEDENCE);
void for_each(token_table const & s, std::function<void(char const *, token_info const&)> const & fn);
void display(std::ostream & out, token_table const & s);
token_table const * find(token_table const & s, char c);
optional<unsigned> get_precedence(token_table const & s, char const * token);
bool is_token(token_table const & s, char const * token);
token_info const * value_of(token_table const & s);
void open_token_table(lua_State * L);
void initialize_token_table();
void finalize_token_table();
}
