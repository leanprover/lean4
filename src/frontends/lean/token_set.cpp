/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "frontends/lean/token_set.h"

namespace lean {
token_set add_command_token(token_set const & s, char const * token) {
    return insert(s, token, token_info(token));
}
token_set add_command_token(token_set const & s, char const * token, char const * val) {
    return insert(s, token, token_info(val));
}
token_set add_token(token_set const & s, char const * token, unsigned prec) {
    return insert(s, token, token_info(token, prec));
}
token_set add_token(token_set const & s, char const * token, char const * val, unsigned prec) {
    return insert(s, token, token_info(val, prec));
}
token_set merge(token_set const & s1, token_set const & s2) {
    return merge(s1, s2);
}
token_set const * find(token_set const & s, char c) {
    return s.find(c);
}
token_info const * value_of(token_set const & s) {
    return s.value();
}
static char const * g_lambda_unicode = "\u03BB";
static char const * g_pi_unicode     = "\u03A0";
static char const * g_forall_unicode = "\u2200";
static char const * g_arrow_unicode  = "\u2192";

// Auxiliary class for creating the initial token set
class init_token_set_fn {
public:
    token_set m_token_set;
    init_token_set_fn() {
            char const * builtin[] = {"fun", "Pi", "let", "in", "have", "show", "by", "from", "(", ")", "{", "}",
                                      ".{", "Type", "...", ",", ".", ":", "calc", ":=", "--", "(*", "(--", "->",
                                      "proof", "qed", "private", nullptr};

            char const * commands[] = {"theorem", "axiom", "variable", "definition", "evaluate", "check",
                                       "print", "variables", "end", "namespace", "section", "import",
                                       "abbreviation", "inductive", "record", "structure", "module", nullptr};

            std::pair<char const *, char const *> aliases[] =
                {{g_lambda_unicode, "fun"}, {"forall", "Pi"}, {g_forall_unicode, "Pi"}, {g_pi_unicode, "Pi"},
                 {g_arrow_unicode, "->"}, {nullptr, nullptr}};

            std::pair<char const *, char const *> cmd_aliases[] =
                {{"parameter", "variable"}, {"parameters", "variables"}, {"lemma", "theorem"},
                 {"hypothesis", "axiom"}, {"conjecture", "axiom"}, {"corollary", "theorem"},
                 {nullptr, nullptr}};

            auto it = builtin;
            while (*it) {
                m_token_set = add_token(m_token_set, *it);
                it++;
            }

            it = commands;
            while (*it) {
                m_token_set = add_command_token(m_token_set, *it);
                ++it;
            }

            auto it2 = aliases;
            while (it2->first) {
                m_token_set = add_token(m_token_set, it2->first, it2->second);
                it2++;
            }

            it2 = cmd_aliases;
            while (it2->first) {
                m_token_set = add_command_token(m_token_set, it2->first, it2->second);
                ++it2;
            }
    }
};
static init_token_set_fn g_init;
token_set mk_default_token_set() { return g_init.m_token_set; }
}
