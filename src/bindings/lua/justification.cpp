/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <lua.hpp>
#include "kernel/justification.h"
#include "bindings/lua/util.h"
#include "bindings/lua/options.h"
#include "bindings/lua/expr.h"
#include "bindings/lua/format.h"
#include "bindings/lua/formatter.h"

namespace lean {
DECL_UDATA(justification)

static int justification_tostring(lua_State * L) {
    std::ostringstream out;
    justification & jst = to_justification(L, 1);
    if (jst) {
        formatter fmt  = get_global_formatter(L);
        options   opts = get_global_options(L);
        out << mk_pair(jst.pp(fmt, opts, nullptr, false), opts);
    } else {
        out << "<null-justification>";
    }
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static int justification_has_children(lua_State * L) {
    lua_pushboolean(L, to_justification(L, 1).has_children());
    return 1;
}

static int justification_is_null(lua_State * L) {
    lua_pushboolean(L, !to_justification(L, 1));
    return 1;
}

/**
   \brief Iterator (closure base function) for justification children. See \c justification_children
*/
static int justification_next_child(lua_State * L) {
    unsigned i    = lua_tointeger(L, lua_upvalueindex(2));
    unsigned num  = objlen(L, lua_upvalueindex(1));
    if (i > num) {
        lua_pushnil(L);
    } else {
        lua_pushinteger(L, i + 1);
        lua_replace(L, lua_upvalueindex(2)); // update i
        lua_rawgeti(L, lua_upvalueindex(1), i); // read children[i]
    }
    return 1;
}

static int justification_children(lua_State * L) {
    buffer<justification_cell*> children;
    to_justification(L, 1).get_children(children);
    lua_newtable(L);
    int i = 1;
    for (auto jcell : children) {
        push_justification(L, justification(jcell));
        lua_rawseti(L, -2, i);
        i = i + 1;
    }
    lua_pushinteger(L, 1);
    lua_pushcclosure(L, &justification_next_child, 2); // create closure with 2 upvalues
    return 1;
}

static int justification_get_main_expr(lua_State * L) {
    return push_expr(L, to_justification(L, 1).get_main_expr());
}

static int justification_pp(lua_State * L) {
    int nargs = lua_gettop(L);
    justification & jst = to_justification(L, 1);
    formatter fmt = get_global_formatter(L);
    options opts  = get_global_options(L);
    bool display_children = true;

    if (nargs == 2) {
        if (lua_isboolean(L, 2)) {
            display_children = lua_toboolean(L, 2);
        } else {
            luaL_checktype(L, 2, LUA_TTABLE);

            lua_pushstring(L, "formatter");
            lua_gettable(L, 2);
            if (is_formatter(L, -1))
                fmt = to_formatter(L, -1);
            lua_pop(L, 1);

            lua_pushstring(L, "options");
            lua_gettable(L, 2);
            if (is_options(L, -1))
                opts = to_options(L, -1);
            lua_pop(L, 1);

            lua_pushstring(L, "display_children");
            lua_gettable(L, 2);
            if (lua_isboolean(L, -1))
                display_children = lua_toboolean(L, -1);
            lua_pop(L, 1);
        }
    }
    return push_format(L, jst.pp(fmt, opts, nullptr, display_children));
}

static int justification_depends_on(lua_State * L) {
    lua_pushboolean(L, depends_on(to_justification(L, 1), to_justification(L, 2)));
    return 1;
}

static int mk_assumption_justification(lua_State * L) {
    return push_justification(L, mk_assumption_justification(luaL_checkinteger(L, 1)));
}

static const struct luaL_Reg justification_m[] = {
    {"__gc",            justification_gc}, // never throws
    {"__tostring",      safe_function<justification_tostring>},
    {"is_null",         safe_function<justification_is_null>},
    {"has_children",    safe_function<justification_has_children>},
    {"children",        safe_function<justification_children>},
    {"get_main_expr",   safe_function<justification_get_main_expr>},
    {"pp",              safe_function<justification_pp>},
    {"depends_on",      safe_function<justification_depends_on>},
    {0, 0}
};

void open_justification(lua_State * L) {
    luaL_newmetatable(L, justification_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, justification_m, 0);

    SET_GLOBAL_FUN(mk_assumption_justification, "mk_assumption_justification");
    SET_GLOBAL_FUN(justification_pred, "is_justification");
}
}
