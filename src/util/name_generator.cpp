/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include <algorithm>
#include "util/name_generator.h"

namespace lean {
static name * g_tmp_prefix = nullptr;
name_generator::name_generator():name_generator(*g_tmp_prefix) {}

name name_generator::next() {
    if (m_next_idx == std::numeric_limits<unsigned>::max()) {
        // avoid overflow
        m_prefix   = name(m_prefix, m_next_idx);
        m_next_idx = 0;
    }
    name r(m_prefix, m_next_idx);
    m_next_idx++;
    return r;
}

void swap(name_generator & a, name_generator & b) {
    swap(a.m_prefix, b.m_prefix);
    std::swap(a.m_next_idx, b.m_next_idx);
}

DECL_UDATA(name_generator)
static int mk_name_generator(lua_State * L) {
    if (lua_gettop(L) == 0)
        return push_name_generator(L, name_generator(*g_tmp_prefix));
    else
        return push_name_generator(L, name_generator(to_name_ext(L, 1)));
}
static int name_generator_next(lua_State * L) { return push_name(L, to_name_generator(L, 1).next()); }
static int name_generator_prefix(lua_State * L) { return push_name(L, to_name_generator(L, 1).prefix()); }
static int name_generator_mk_child(lua_State * L) { return push_name_generator(L, to_name_generator(L, 1).mk_child()); }
static const struct luaL_Reg name_generator_m[] = {
    {"__gc",     name_generator_gc}, // never throws
    {"next",     safe_function<name_generator_next>},
    {"prefix",   safe_function<name_generator_prefix>},
    {"mk_child", safe_function<name_generator_mk_child>},
    {0, 0}
};

void open_name_generator(lua_State * L) {
    luaL_newmetatable(L, name_generator_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, name_generator_m, 0);

    SET_GLOBAL_FUN(mk_name_generator,   "name_generator");
    SET_GLOBAL_FUN(name_generator_pred, "is_name_generator");
}

void initialize_name_generator() {
    g_tmp_prefix = new name(name::mk_internal_unique_name());
}

void finalize_name_generator() {
    delete g_tmp_prefix;
}
}
