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
token_set mk_default_token_set();
token_set add_command_token(token_set const & s, char const * token);
token_set add_token(token_set const & s, char const * token, unsigned prec = 0);
token_set add_token(token_set const & s, char const * token, char const * val, unsigned prec = 0);
token_set merge(token_set const & s1, token_set const & s2);
token_set const * find(token_set const & s, char c);
token_info const * value_of(token_set const & s);
}
