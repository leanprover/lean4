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

namespace lean {
class token_info {
    bool        m_command;
    name        m_value;
    unsigned    m_precedence;
public:
    token_info():m_command(true) {}
    token_info(char const * val):m_command(true), m_value(val), m_precedence(0) {}
    token_info(char const * val, unsigned prec):m_command(false), m_value(val), m_precedence(prec) {}
    bool is_command() const { return m_command; }
    name const & value() const { return m_value; }
    unsigned precedence() const { return m_precedence; }
};

typedef ctrie<token_info> token_set;
token_set mk_token_set();
token_set mk_default_token_set();
token_set add_command_token(token_set const & s, char const * token);
token_set add_command_token(token_set const & s, char const * token, char const * val);
token_set add_token(token_set const & s, char const * token, unsigned prec = 0);
token_set add_token(token_set const & s, char const * token, char const * val, unsigned prec = 0);
void for_each(token_set const & s, std::function<void(char const *, token_info const&)> const & fn);
token_set const * find(token_set const & s, char c);
token_info const * value_of(token_set const & s);
void open_token_set(lua_State * L);
}
