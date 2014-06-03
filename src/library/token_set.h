/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <string>
#include "util/trie.h"

namespace lean {

/** \brief Set of tokens and their precedences. This information is used by the scanner. */
class token_set {
    class info {
        bool        m_command;
        std::string m_value;
        unsigned    m_precedence;
    public:
        info():m_command(true) {}
        info(char const * val):m_command(true), m_value(val), m_precedence(0) {}
        info(char const * val, unsigned prec):m_command(false), m_value(val), m_precedence(prec) {}
        bool is_command() const { return m_command; }
        std::string const & value() const { return m_value; }
        unsigned precedence() const { return m_precedence; }
    };
    ctrie<info> m_tokens;
    explicit token_set(ctrie<info> const & t):m_tokens(t) {}
    friend class init_token_set_fn;
    token_set(bool) {} // NOLINT
public:
    token_set();
    token_set add_command_token(char const * token) const;
    token_set add_token(char const * token, unsigned prec = 0) const;
    token_set add_token(char const * token, char const * val, unsigned prec = 0) const;
    token_set merge(token_set const & s) const;
    optional<token_set> find(char c) const;
    optional<info> value() const;
};
}
