/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <lua.hpp>
#include "util/splay_map.h"
#include "bindings/lua/util.h"

#include "bindings/lua/expr.h"
#include "library/expr_lt.h"

namespace lean {
/**
   \brief Reference to Lua object.
*/
class lua_ref {
    lua_State * m_state;
    int         m_ref;
public:
    lua_ref():m_state(nullptr) {}

    lua_ref(lua_State * L, int i) {
        lean_assert(L);
        m_state = L;
        lua_pushvalue(m_state, i);
        m_ref   = luaL_ref(m_state, LUA_REGISTRYINDEX);
    }

    lua_ref(lua_ref const & r) {
        m_state = r.m_state;
        if (m_state) {
            r.push();
            m_ref   = luaL_ref(m_state, LUA_REGISTRYINDEX);
        }
    }

    lua_ref(lua_ref && r) {
        m_state = r.m_state;
        m_ref   = r.m_ref;
        r.m_state = nullptr;
    }

    ~lua_ref() {
        if (m_state)
            luaL_unref(m_state, LUA_REGISTRYINDEX, m_ref);
    }

    lua_ref & operator=(lua_ref const & r) {
        if (m_ref == r.m_ref)
            return *this;
        if (m_state)
            luaL_unref(m_state, LUA_REGISTRYINDEX, m_ref);
        m_state = r.m_state;
        if (m_state) {
            r.push();
            m_ref   = luaL_ref(m_state, LUA_REGISTRYINDEX);
        }
        return *this;
    }

    void push() const {
        lean_assert(m_state);
        lua_rawgeti(m_state, LUA_REGISTRYINDEX, m_ref);
    }

    lua_State * get_state() const {
        return m_state;
    }
};

struct lua_lt_proc {
    int operator()(lua_ref const & r1, lua_ref const & r2) const {
        lean_assert(r1.get_state() == r2.get_state());
        lua_State * L = r1.get_state();
        r1.push();
        r2.push();
        int r;
        if (lessthan(L, -2, -1)) {
            r = -1;
        } else if (lessthan(L, -1, -2)) {
            r = 1;
        } else if (equal(L, -2, -1)) {
            r = 0;
        } else {
            throw exception("'<' is not a total order for the elements inserted on the table");
        }
        lua_pop(L, 2);
        return r;
    }
};

typedef splay_map<lua_ref, lua_ref, lua_lt_proc> lua_splay_map;

constexpr char const * splay_map_mt = "splay_map.mt";

bool is_splay_map(lua_State * L, int idx) {
    return testudata(L, idx, splay_map_mt);
}

lua_splay_map & to_splay_map(lua_State * L, int idx) {
    return *static_cast<lua_splay_map*>(luaL_checkudata(L, idx, splay_map_mt));
}

int push_splay_map(lua_State * L, lua_splay_map const & o) {
    void * mem = lua_newuserdata(L, sizeof(lua_splay_map));
    new (mem) lua_splay_map(o);
    luaL_getmetatable(L, splay_map_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int mk_splay_map(lua_State * L) {
    lua_splay_map r;
    return push_splay_map(L, r);
}

static int splay_map_gc(lua_State * L) {
    to_splay_map(L, 1).~lua_splay_map();
    return 0;
}

static int splay_map_size(lua_State * L) {
    lua_pushinteger(L, to_splay_map(L, 1).size());
    return 1;
}

static int splay_map_contains(lua_State * L) {
    lua_pushboolean(L, to_splay_map(L, 1).contains(lua_ref(L, 2)));
    return 1;
}

static int splay_map_empty(lua_State * L) {
    lua_pushboolean(L, to_splay_map(L, 1).empty());
    return 1;
}

static int splay_map_insert(lua_State * L) {
    to_splay_map(L, 1).insert(lua_ref(L, 2), lua_ref(L, 3));
    return 0;
}

static int splay_map_erase(lua_State * L) {
    to_splay_map(L, 1).erase(lua_ref(L, 2));
    return 0;
}

static int splay_map_find(lua_State * L) {
    lua_splay_map & m = to_splay_map(L, 1);
    lua_ref * val = m.splay_find(lua_ref(L, 2));
    if (val) {
        lean_assert(val->get_state() == L);
        val->push();
    } else {
        lua_pushnil(L);
    }
    return 1;
}

static int splay_map_copy(lua_State * L) {
    return push_splay_map(L, to_splay_map(L, 1));
}

static int splay_map_pred(lua_State * L) {
    lua_pushboolean(L, is_splay_map(L, 1));
    return 1;
}

static int splay_map_for_each(lua_State * L) {
    // Remark: we take a copy of the map to make sure
    // for_each will not crash if the map is updated while being
    // traversed.
    // The copy operation is very cheap O(1).
    lua_splay_map m(to_splay_map(L, 1)); // map
    luaL_checktype(L, 2, LUA_TFUNCTION); // user-fun
    m.for_each([&](lua_ref const & k, lua_ref const & v) {
        lua_pushvalue(L, 2); // push user-fun
        k.push();
        v.push();
        pcall(L, 2, 0, 0);
        });
    return 0;
}

static const struct luaL_Reg splay_map_m[] = {
    {"__gc",            splay_map_gc}, // never throws
    {"__len",           safe_function<splay_map_size> },
    {"contains",        safe_function<splay_map_contains>},
    {"size",            safe_function<splay_map_size>},
    {"empty",           safe_function<splay_map_empty>},
    {"insert",          safe_function<splay_map_insert>},
    {"erase",           safe_function<splay_map_erase>},
    {"find",            safe_function<splay_map_find>},
    {"copy",            safe_function<splay_map_copy>},
    {"for_each",        safe_function<splay_map_for_each>},
    {0, 0}
};

void open_splay_map(lua_State * L) {
    luaL_newmetatable(L, splay_map_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, splay_map_m, 0);

    SET_GLOBAL_FUN(mk_splay_map,          "splay_map");
    SET_GLOBAL_FUN(splay_map_pred,        "is_splay_map");
}
}
