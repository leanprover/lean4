/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include "kernel/abstract.h"
#include "frontends/lean/parser_bindings.h"

namespace lean {
static char g_parser_key;
void set_global_parser(lua_State * L, parser * p) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_parser_key));
    lua_pushlightuserdata(L, static_cast<void *>(p));
    lua_settable(L, LUA_REGISTRYINDEX);
}

parser * get_global_parser_ptr(lua_State * L) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_parser_key));
    lua_gettable(L, LUA_REGISTRYINDEX);
    if (!lua_islightuserdata(L, -1))
        return nullptr;
    parser * p = static_cast<parser*>(const_cast<void*>(lua_topointer(L, -1)));
    lua_pop(L, 1);
    return p;
}

parser & get_global_parser(lua_State * L) {
    parser * p = get_global_parser_ptr(L);
    if (p == nullptr)
        throw exception("there is no Lean parser on the Lua stack");
    return *p;
}

scoped_set_parser::scoped_set_parser(lua_State * L, parser & p):m_state(L) {
    m_old = get_global_parser_ptr(L);
    set_global_parser(L, &p);
}
scoped_set_parser::~scoped_set_parser() {
    set_global_parser(m_state, m_old);
}

static unsigned to_rbp(lua_State * L, int idx) {
    int nargs = lua_gettop(L);
    return idx < nargs ? 0 : lua_tointeger(L, idx);
}

typedef pair<local_environment, std::vector<expr>> local_scope_cell;
typedef std::shared_ptr<local_scope_cell> local_scope;
DECL_UDATA(local_scope);
static const struct luaL_Reg local_scope_m[] = {
    {"__gc",  local_scope_gc},
    {0, 0}
};
int push_local_scope_ext(lua_State * L, local_environment const & lenv, buffer<expr> const & ps) {
    local_scope r = std::make_shared<local_scope_cell>();
    r->first = lenv;
    for (auto const & p : ps)
        r->second.push_back(p);
    return push_local_scope(L, r);
}

static void open_local_scope(lua_State * L) {
    luaL_newmetatable(L, local_scope_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, local_scope_m, 0);

    SET_GLOBAL_FUN(local_scope_pred, "is_local_scope");
}

#define gparser get_global_parser(L)

static int parse_level(lua_State * L) {  return push_level(L, gparser.parse_level(to_rbp(L, 1))); }
static int parse_expr(lua_State * L) { return push_expr(L, gparser.parse_expr(to_rbp(L, 1))); }
static int parse_led(lua_State * L) { return push_expr(L, gparser.parse_led(to_expr(L, 1))); }
static int parse_binders(lua_State * L) {
    buffer<expr> ps;
    unsigned rbp = 0;
    auto lenv    = gparser.parse_binders(ps, rbp);
    return push_local_scope_ext(L, lenv, ps);
}
static int parse_binder(lua_State * L) {
    buffer<expr> ps;
    unsigned rbp = 0;
    ps.push_back(gparser.parse_binder(rbp));
    return push_local_scope_ext(L, gparser.env(), ps);
}
static int parse_scoped_expr(lua_State * L) {
    local_scope const & s = to_local_scope(L, 1);
    unsigned rbp    = to_rbp(L, 2);
    return push_expr(L, gparser.parse_scoped_expr(s->second.size(), s->second.data(), s->first, rbp));
}
static int lambda_abstract(lua_State * L) {
    int nargs = lua_gettop(L);
    local_scope const & s = to_local_scope(L, 1);
    expr const & e = to_expr(L, 2);
    expr r;
    bool using_cache = false;
    if (nargs == 2)
        r = gparser.rec_save_pos(Fun(s->second.size(), s->second.data(), e, using_cache), gparser.pos_of(e));
    else
        r = gparser.rec_save_pos(Fun(s->second.size(), s->second.data(), e, using_cache), pos_info(lua_tointeger(L, 3), lua_tointeger(L, 4)));
    return push_expr(L, r);
}
static int next(lua_State * L) { gparser.next(); return 0; }
static int curr(lua_State * L) { return push_integer(L, static_cast<unsigned>(gparser.curr())); }
static int curr_is_token(lua_State * L) { return push_boolean(L, gparser.curr_is_token(to_name_ext(L, 1))); }
static int curr_is_token_or_id(lua_State * L) { return push_boolean(L, gparser.curr_is_token_or_id(to_name_ext(L, 1))); }
static int curr_is_identifier(lua_State * L) { return push_boolean(L, gparser.curr_is_identifier()); }
static int curr_is_numeral(lua_State * L) { return push_boolean(L, gparser.curr_is_numeral()); }
static int curr_is_string(lua_State * L) { return push_boolean(L, gparser.curr_is_string()); }
static int curr_is_keyword(lua_State * L) { return push_boolean(L, gparser.curr_is_keyword()); }
static int curr_is_command(lua_State * L) { return push_boolean(L, gparser.curr_is_command()); }
static int curr_is_quoted_symbol(lua_State * L) { return push_boolean(L, gparser.curr_is_quoted_symbol()); }
static int check_token_next(lua_State * L) { gparser.check_token_next(to_name_ext(L, 1), lua_tostring(L, 2)); return 0; }
static int check_id_next(lua_State * L) { return push_name(L, gparser.check_id_next(lua_tostring(L, 1))); }
static int pos(lua_State * L) {
    auto pos = gparser.pos();
    push_integer(L, pos.first);
    push_integer(L, pos.second);
    return 2;
}
static int save_pos(lua_State * L) {
    return push_expr(L, gparser.save_pos(to_expr(L, 1), pos_info(lua_tointeger(L, 2), lua_tointeger(L, 3))));
}
static int pos_of(lua_State * L) {
    int nargs = lua_gettop(L);
    pos_info pos;
    if (nargs == 1)
        pos = gparser.pos_of(to_expr(L, 1));
    else
        pos = gparser.pos_of(to_expr(L, 1), pos_info(lua_tointeger(L, 2), lua_tointeger(L, 3)));
    push_integer(L, pos.first);
    push_integer(L, pos.second);
    return 2;
}
static int env(lua_State * L) { return push_environment(L, gparser.env()); }
static int ios(lua_State * L) { return push_io_state(L, gparser.ios()); }

void open_parser(lua_State * L) {
    open_local_scope(L);

    lua_newtable(L);
    SET_FUN(parse_expr,            "parse_expr");
    SET_FUN(parse_level,           "parse_level");
    SET_FUN(parse_led,             "parse_led");
    SET_FUN(parse_binders,         "parse_binders");
    SET_FUN(parse_binder,          "parse_binder");
    SET_FUN(parse_scoped_expr,     "parse_scoped_expr");
    SET_FUN(lambda_abstract,       "lambda_abstract");
    SET_FUN(lambda_abstract,       "abstract");
    SET_FUN(next,                  "next");
    SET_FUN(curr,                  "curr");
    SET_FUN(curr_is_token,         "curr_is_token");
    SET_FUN(curr_is_token_or_id,   "curr_is_token_or_id");
    SET_FUN(curr_is_identifier,    "curr_is_identifier");
    SET_FUN(curr_is_numeral,       "curr_is_numeral");
    SET_FUN(curr_is_string,        "curr_is_string");
    SET_FUN(curr_is_keyword,       "curr_is_keyword");
    SET_FUN(curr_is_command,       "curr_is_command");
    SET_FUN(curr_is_quoted_symbol, "curr_is_quoted_symbol");
    SET_FUN(check_token_next,      "check_token_next");
    SET_FUN(check_id_next,         "check_id_next");
    SET_FUN(pos,                   "pos");
    SET_FUN(save_pos,              "save_pos");
    SET_FUN(pos_of,                "pos_of");
    SET_FUN(env,                   "env");
    SET_FUN(ios,                   "ios");
    lua_setglobal(L, "parser");

    lua_newtable(L);
    SET_ENUM("Keyword",         scanner::token_kind::Keyword);
    SET_ENUM("CommandKeyword",  scanner::token_kind::CommandKeyword);
    SET_ENUM("ScriptBlock",     scanner::token_kind::ScriptBlock);
    SET_ENUM("Identifier",      scanner::token_kind::Identifier);
    SET_ENUM("Numeral",         scanner::token_kind::Numeral);
    SET_ENUM("Decimal",         scanner::token_kind::Decimal);
    SET_ENUM("String",          scanner::token_kind::String);
    SET_ENUM("QuotedSymbol",    scanner::token_kind::QuotedSymbol);
    lua_setglobal(L, "token_kind");
}
}
