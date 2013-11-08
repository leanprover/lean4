/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <lua.hpp>
#include <cstring>
#include "util/debug.h"
#include "util/sexpr/format.h"
#include "bindings/lua/util.h"
#include "bindings/lua/name.h"
#include "bindings/lua/numerics.h"

namespace lean {
constexpr char const * format_mt = "format.mt";

int push_format(lua_State * L, format const & e) {
    void * mem = lua_newuserdata(L, sizeof(format));
    new (mem) format(e);
    luaL_getmetatable(L, format_mt);
    lua_setmetatable(L, -2);
    return 1;
}

bool is_format(lua_State * L, int idx) {
    return testudata(L, idx, format_mt);
}

format & to_format(lua_State * L, int idx) {
    return *static_cast<format*>(luaL_checkudata(L, idx, format_mt));
}

format to_format_elem(lua_State * L, int idx) {
    if (is_format(L, idx))
        return to_format(L, idx);
    else if (lua_isnumber(L, idx))
        return format(static_cast<int>(lua_tonumber(L, idx)));
    else if (is_name(L, idx))
        return format(to_name(L, idx));
    else if (is_mpz(L, idx))
        return format(to_mpz(L, idx));
    else if (is_mpq(L, idx))
        return format(to_mpq(L, idx));
    else
        return format(lua_tostring(L, idx));
}

static int format_gc(lua_State * L) {
    to_format(L, 1).~format();
    return 0;
}

static int format_tostring(lua_State * L) {
    std::ostringstream out;
    out << to_format(L, 1);
    lua_pushfstring(L, out.str().c_str());
    return 1;
}

static int format_concat(lua_State * L) {
    return push_format(L, compose(to_format_elem(L, 1), to_format_elem(L, 2)));
}

static int mk_format(lua_State * L) {
    format r;
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        r = format();
    } else {
        int i = nargs;
        r = to_format_elem(L, i);
        i--;
        for (; i >= 1; i--) {
            r = compose(to_format_elem(L, i), r);
        }
    }
    return push_format(L, r);
}

static int format_nest(lua_State * L) {
    return push_format(L, nest(luaL_checkinteger(L, 2), to_format(L, 1)));
}

static int format_group(lua_State * L) {
    return push_format(L, group(to_format(L, 1)));
}

static int format_highlight(lua_State * L) {
    char const * color_str = luaL_checkstring(L, 2);
    format::format_color color;
    if (strcmp(color_str, "red") == 0) {
        color = format::RED;
    } else if (strcmp(color_str, "green") == 0) {
        color = format::GREEN;
    } else if (strcmp(color_str, "orange") == 0) {
        color = format::ORANGE;
    } else if (strcmp(color_str, "blue") == 0) {
        color = format::BLUE;
    } else if (strcmp(color_str, "cyan") == 0) {
        color = format::CYAN;
    } else if (strcmp(color_str, "grey") == 0) {
        color = format::GREY;
    } else {
        return luaL_error(L, "unknown color '%'", color_str);
    }
    return push_format(L, highlight(to_format(L, 1), color));
}

static int format_line(lua_State * L) { return push_format(L, line()); }
static int format_space(lua_State * L) { return push_format(L, space()); }

static int format_pred(lua_State * L) {
    lua_pushboolean(L, is_format(L, 1));
    return 1;
}

static const struct luaL_Reg format_m[] = {
    {"__gc",            format_gc}, // never throws
    {"__tostring",      safe_function<format_tostring>},
    {"__concat",        safe_function<format_concat>},
    {"nest",            safe_function<format_nest>},
    {"group",           safe_function<format_group>},
    {"highlight",       safe_function<format_highlight>},
    {0, 0}
};

void open_format(lua_State * L) {
    luaL_newmetatable(L, format_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, format_m, 0);

    set_global_function<mk_format>(L, "format");
    set_global_function<format_line>(L, "line");
    set_global_function<format_space>(L, "space");
    set_global_function<format_pred>(L, "is_format");
}
}
