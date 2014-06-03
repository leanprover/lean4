/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/token_set.h"

namespace lean {
token_set token_set::add_command_token(char const * token) const { return token_set(insert(m_tokens, token, info(token))); }
token_set token_set::add_token(char const * token, unsigned prec) const { return token_set(insert(m_tokens, token, info(token, prec))); }
token_set token_set::add_token(char const * token, char const * val, unsigned prec) const {
    return token_set(insert(m_tokens, token, info(val, prec)));
}
token_set token_set::merge(token_set const & s) const { return token_set(::lean::merge(m_tokens, s.m_tokens)); }
optional<token_set> token_set::find(char c) const {
    auto r = m_tokens.find(c);
    return r ? optional<token_set>(token_set(*r)) : optional<token_set>();
}
optional<token_set::info> token_set::value() const { return m_tokens.value(); }

static char const * g_lambda_unicode = "\u03BB";
static char const * g_pi_unicode     = "\u03A0";
static char const * g_forall_unicode = "\u2200";
static char const * g_arrow_unicode  = "\u2192";

// Auxiliary class for creating the initial token set
class init_token_set_fn {
public:
    token_set m_token_set;
    init_token_set_fn():m_token_set(true) {
        char const * builtin[] = {"fun", "forall", "let", "in", "have", "show", "by", "from", "(", ")", "{", "}",
                                  ".{", "Type", "...", ",", ".", ":", "calc", ":=", "--", "(*", "(--", "->", 0};
        char const ** it = builtin;
        while (*it) {
            m_token_set = m_token_set.add_token(*it);
            it++;
        }
        m_token_set = m_token_set.add_token(g_lambda_unicode, "fun");
        m_token_set = m_token_set.add_token(g_forall_unicode, "forall");
        m_token_set = m_token_set.add_token(g_pi_unicode,     "forall");
        m_token_set = m_token_set.add_token(g_arrow_unicode,  "->");
    }
};
static init_token_set_fn g_init;
token_set::token_set():token_set(g_init.m_token_set) {}
}
