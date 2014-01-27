/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/io_state_stream.h"
#include "frontends/lean/parser_imp.h"
#include "frontends/lean/notation.h"

namespace lean {
static char g_set_parser_key;
/** \brief Return a reference to the parser object */
parser_imp * get_parser(lua_State * L) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_set_parser_key));
    lua_gettable(L, LUA_REGISTRYINDEX);
    if (lua_islightuserdata(L, -1)) {
        auto r = static_cast<parser_imp*>(lua_touserdata(L, -1));
        lua_pop(L, 1);
        return r;
    }
    lua_pop(L, 1);
    return nullptr;
}

set_parser::set_parser(script_state * S, parser_imp * ptr) {
    if (S) {
        m_state = S->to_weak_ref();
        S->apply([&](lua_State * L) {
                m_prev  = get_parser(L);
                lua_pushlightuserdata(L, static_cast<void *>(&g_set_parser_key));
                lua_pushlightuserdata(L, ptr);
                lua_settable(L, LUA_REGISTRYINDEX);
            });
    }
}
set_parser::~set_parser() {
    if (!m_state.expired()) {
        script_state S(m_state);
        S.apply([&](lua_State * L) {
                lua_pushlightuserdata(L, static_cast<void *>(&g_set_parser_key));
                lua_pushlightuserdata(L, m_prev);
                lua_settable(L, LUA_REGISTRYINDEX);
            });
    }
}

static char g_parser_expr_macros_key;
static char g_parser_tactic_macros_key;
static char g_parser_cmd_macros_key;
DECL_UDATA(macros)

macros & get_macros(lua_State * L, char * key) {
    lua_pushlightuserdata(L, static_cast<void *>(key));
    lua_gettable(L, LUA_REGISTRYINDEX);
    if (lua_isnil(L, -1)) {
        lua_pop(L, 1);
        lua_pushlightuserdata(L, static_cast<void *>(key));
        push_macros(L, macros());
        lua_settable(L, LUA_REGISTRYINDEX);
        lua_pushlightuserdata(L, static_cast<void *>(key));
        lua_gettable(L, LUA_REGISTRYINDEX);
    }
    lean_assert(is_macros(L, -1));
    macros & r = to_macros(L, -1);
    lua_pop(L, 1);
    return r;
}

macros & get_expr_macros(lua_State * L)   { return get_macros(L, &g_parser_expr_macros_key); }
macros & get_tactic_macros(lua_State * L) { return get_macros(L, &g_parser_tactic_macros_key); }
macros & get_cmd_macros(lua_State * L)    { return get_macros(L, &g_parser_cmd_macros_key); }

void mk_macro(lua_State * L, macros & mtable) {
    int nargs = lua_gettop(L);
    name macro_name = to_name_ext(L, 1);
    unsigned prec = nargs == 4 ? lua_tointeger(L, 4) : g_app_precedence;
    luaL_checktype(L, 3, LUA_TFUNCTION); // user-fun
    buffer<macro_arg_kind> arg_kind_buffer;
    int n = objlen(L, 2);
    for (int i = 1; i <= n; i++) {
        lua_rawgeti(L, 2, i);
        arg_kind_buffer.push_back(static_cast<macro_arg_kind>(luaL_checkinteger(L, -1)));
        lua_pop(L, 1);
    }
    list<macro_arg_kind> arg_kinds = to_list(arg_kind_buffer.begin(), arg_kind_buffer.end());
    mtable.insert(mk_pair(macro_name, macro(arg_kinds, luaref(L, 3), prec)));
}

int mk_macro(lua_State * L) {
    mk_macro(L, get_expr_macros(L));
    return 0;
}

int mk_cmd_macro(lua_State * L) {
    mk_macro(L, get_cmd_macros(L));
    name macro_name = to_name_ext(L, 1);
    parser_imp * ptr = get_parser(L);
    if (!ptr)
        throw exception("invalid cmd_macro, it is not in the context of a Lean parser");
    // Make sure macro_name is a CommandId.
    ptr->m_scanner.add_command_keyword(macro_name);
    if (ptr->m_curr == scanner::token::Id && ptr->curr_name() == macro_name) {
        ptr->m_curr = scanner::token::CommandId;
    }
    return 0;
}

int mk_tactic_macro(lua_State * L) {
    mk_macro(L, get_tactic_macros(L));
    return 0;
}

static const struct luaL_Reg macros_m[] = {
    {"__gc",            macros_gc}, // never throws
    {0, 0}
};

void open_macros(lua_State * L) {
    luaL_newmetatable(L, macros_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, macros_m, 0);
    SET_GLOBAL_FUN(macros_pred, "is_macros");
    SET_GLOBAL_FUN(mk_macro, "macro");
    SET_GLOBAL_FUN(mk_cmd_macro, "cmd_macro");
    SET_GLOBAL_FUN(mk_tactic_macro, "tactic_macro");

    lua_newtable(L);
    SET_ENUM("Expr",       macro_arg_kind::Expr);
    SET_ENUM("Exprs",      macro_arg_kind::Exprs);
    SET_ENUM("Parameters", macro_arg_kind::Parameters);
    SET_ENUM("Id",         macro_arg_kind::Id);
    SET_ENUM("Ids",        macro_arg_kind::Ids);
    SET_ENUM("String",     macro_arg_kind::String);
    SET_ENUM("Int",        macro_arg_kind::Int);
    SET_ENUM("Comma",      macro_arg_kind::Comma);
    SET_ENUM("Assign",     macro_arg_kind::Assign);
    SET_ENUM("Tactic",     macro_arg_kind::Tactic);
    SET_ENUM("Tactics",    macro_arg_kind::Tactics);
    lua_setglobal(L, "macro_arg");
}
}
