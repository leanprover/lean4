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
token_set const * find(token_set const & s, char c) {
    return s.find(c);
}
token_info const * value_of(token_set const & s) {
    return s.value();
}
void for_each(token_set const & s, std::function<void(char const *, token_info const &)> const & fn) {
    s.for_each([&](unsigned num, char const * keys, token_info const & info) {
            buffer<char> str;
            str.append(num, keys);
            str.push_back(0);
            fn(str.data(), info);
        });
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
token_set mk_token_set() { return token_set(); }
token_set mk_default_token_set() { return g_init.m_token_set; }

DECL_UDATA(token_set)
static int mk_token_set(lua_State * L) { return push_token_set(L, mk_token_set()); }
static int mk_default_token_set(lua_State * L) { return push_token_set(L, mk_default_token_set()); }
static int add_command_token(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_token_set(L, add_command_token(to_token_set(L, 1), lua_tostring(L, 2)));
    else
        return push_token_set(L, add_command_token(to_token_set(L, 1), lua_tostring(L, 2), lua_tostring(L, 3)));
}
static int add_token(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 3)
        return push_token_set(L, add_token(to_token_set(L, 1), lua_tostring(L, 2), lua_tonumber(L, 3)));
    else
        return push_token_set(L, add_token(to_token_set(L, 1), lua_tostring(L, 2), lua_tostring(L, 3), lua_tonumber(L, 4)));
}
static int merge(lua_State * L) {
    return push_token_set(L, merge(to_token_set(L, 1), to_token_set(L, 2)));
}
static int find(lua_State * L) {
    char k;
    if (lua_isnumber(L, 2)) {
        k = lua_tonumber(L, 2);
    } else {
        char const * str = lua_tostring(L, 2);
        if (strlen(str) != 1)
            throw exception("arg #2 must be a string of length 1");
        k = str[0];
    }
    auto it = to_token_set(L, 1).find(k);
    if (it)
        return push_token_set(L, *it);
    else
        return push_nil(L);
}
static int value_of(lua_State * L) {
    auto it = value_of(to_token_set(L, 1));
    if (it) {
        push_boolean(L, it->is_command());
        push_name(L, it->value());
        push_integer(L, it->precedence());
        return 3;
    } else {
        push_nil(L);
        return 1;
    }
}
static int for_each(lua_State * L) {
    token_set const & t = to_token_set(L, 1);
    luaL_checktype(L, 2, LUA_TFUNCTION); // user-fun
    for_each(t, [&](char const * k, token_info const & info) {
            lua_pushvalue(L, 2);
            lua_pushstring(L, k);
            lua_pushboolean(L, info.is_command());
            push_name(L, info.value());
            lua_pushinteger(L, info.precedence());
            pcall(L, 4, 0, 0);
        });
    return 0;
}

static const struct luaL_Reg token_set_m[] = {
    {"__gc",              token_set_gc},
    {"add_command_token", safe_function<add_command_token>},
    {"add_token",         safe_function<add_token>},
    {"merge",             safe_function<merge>},
    {"find",              safe_function<find>},
    {"value_of",          safe_function<value_of>},
    {"for_each",          safe_function<for_each>},
    {0, 0}
};

void open_token_set(lua_State * L) {
    luaL_newmetatable(L, token_set_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, token_set_m, 0);

    SET_GLOBAL_FUN(token_set_pred,       "is_token_set");
    SET_GLOBAL_FUN(mk_default_token_set, "default_token_set");
    SET_GLOBAL_FUN(mk_token_set,         "token_set");
}
}
