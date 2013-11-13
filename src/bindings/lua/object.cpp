/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <lua.hpp>
#include "util/sexpr/options.h"
#include "kernel/object.h"
#include "kernel/formatter.h"
#include "bindings/lua/util.h"
#include "bindings/lua/name.h"
#include "bindings/lua/options.h"
#include "bindings/lua/level.h"
#include "bindings/lua/expr.h"
#include "bindings/lua/formatter.h"

namespace lean {
constexpr char const * object_mt = "object.mt";

bool is_object(lua_State * L, int idx) {
    return testudata(L, idx, object_mt);
}

object & to_object(lua_State * L, int idx) {
    return *static_cast<object*>(luaL_checkudata(L, idx, object_mt));
}

object & to_nonnull_object(lua_State * L, int idx) {
    object & r = to_object(L, idx);
    if (!r)
        throw exception("non-null kernel object expected");
    return r;
}

int push_object(lua_State * L, object const & o) {
    void * mem = lua_newuserdata(L, sizeof(object));
    new (mem) object(o);
    luaL_getmetatable(L, object_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int object_gc(lua_State * L) {
    to_object(L, 1).~object();
    return 0;
}

static int object_is_null(lua_State * L) {
    lua_pushboolean(L, !to_object(L, 1));
    return 1;
}

static int object_keyword(lua_State * L) {
    lua_pushstring(L, to_nonnull_object(L, 1).keyword());
    return 1;
}

static int object_has_name(lua_State * L) {
    lua_pushboolean(L, to_nonnull_object(L, 1).has_name());
    return 1;
}

static int object_get_name(lua_State * L) {
    if (!to_nonnull_object(L, 1).has_name())
        throw exception("kernel object does not have a name");
    return push_name(L, to_nonnull_object(L, 1).get_name());
}

static int object_has_type(lua_State * L) {
    lua_pushboolean(L, to_nonnull_object(L, 1).has_type());
    return 1;
}

static int object_get_type(lua_State * L) {
    if (!to_nonnull_object(L, 1).has_type())
        throw exception("kernel object does not have a type");
    return push_expr(L, to_nonnull_object(L, 1).get_type());
}

static int object_has_cnstr_level(lua_State * L) {
    lua_pushboolean(L, to_nonnull_object(L, 1).has_cnstr_level());
    return 1;
}

static int object_get_cnstr_level(lua_State * L) {
    if (!to_nonnull_object(L, 1).has_cnstr_level())
        throw exception("kernel object does not have a constraint level");
    return push_level(L, to_nonnull_object(L, 1).get_cnstr_level());
}

static int object_get_value(lua_State * L) {
    if (!to_nonnull_object(L, 1).is_definition())
        throw exception("kernel object is not a definition/theorem");
    return push_expr(L, to_nonnull_object(L, 1).get_value());
}

static int object_get_weight(lua_State * L) {
    if (!to_nonnull_object(L, 1).is_definition())
        throw exception("kernel object is not a definition");
    lua_pushinteger(L, to_nonnull_object(L, 1).get_weight());
    return 1;
}

#define OBJECT_PRED(P)                                  \
static int object_ ## P(lua_State * L) {                \
    lua_pushboolean(L, to_nonnull_object(L, 1).P());    \
    return 1;                                           \
}

OBJECT_PRED(is_definition)
OBJECT_PRED(is_opaque)
OBJECT_PRED(is_axiom)
OBJECT_PRED(is_theorem)
OBJECT_PRED(is_var_decl)
OBJECT_PRED(is_builtin)
OBJECT_PRED(is_builtin_set)

static int object_in_builtin_set(lua_State * L) {
    lua_pushboolean(L, to_nonnull_object(L, 1).in_builtin_set(to_expr(L, 2)));
    return 1;
}

static int object_pred(lua_State * L) {
    lua_pushboolean(L, is_object(L, 1));
    return 1;
}

static int object_tostring(lua_State * L) {
    std::ostringstream out;
    formatter fmt = get_global_formatter(L);
    options opts  = get_global_options(L);
    object & obj  = to_object(L, 1);
    if (obj)
        out << mk_pair(fmt(to_object(L, 1), opts), opts);
    else
        out << "<null-kernel-object>";
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static const struct luaL_Reg object_m[] = {
    {"__gc",            object_gc}, // never throws
    {"__tostring",      safe_function<object_tostring>},
    {"is_null",         safe_function<object_is_null>},
    {"keyword",         safe_function<object_keyword>},
    {"has_name",        safe_function<object_has_name>},
    {"get_name",        safe_function<object_get_name>},
    {"has_type",        safe_function<object_has_type>},
    {"get_type",        safe_function<object_get_type>},
    {"has_cnstr_level", safe_function<object_has_cnstr_level>},
    {"get_cnstr_level", safe_function<object_get_cnstr_level>},
    {"is_definition",   safe_function<object_is_definition>},
    {"is_opaque",       safe_function<object_is_opaque>},
    {"get_value",       safe_function<object_get_value>},
    {"get_weight",      safe_function<object_get_weight>},
    {"is_axiom",        safe_function<object_is_axiom>},
    {"is_theorem",      safe_function<object_is_theorem>},
    {"is_var_decl",     safe_function<object_is_var_decl>},
    {"is_builtin",      safe_function<object_is_builtin>},
    {"is_builtin_set",  safe_function<object_is_builtin_set>},
    {"in_builtin_set",  safe_function<object_in_builtin_set>},
    {0, 0}
};

void open_object(lua_State * L) {
    luaL_newmetatable(L, object_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, object_m, 0);

    SET_GLOBAL_FUN(object_pred, "is_kernel_object");
}
}
