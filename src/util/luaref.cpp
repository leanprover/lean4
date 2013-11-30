/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/luaref.h"
#include "util/debug.h"

namespace lean {
luaref::luaref(lua_State * L, int i) {
    lean_assert(L);
    m_state = L;
    lua_pushvalue(m_state, i);
    m_ref   = luaL_ref(m_state, LUA_REGISTRYINDEX);
}

luaref::luaref(luaref const & r) {
    m_state = r.m_state;
    if (m_state) {
        r.push();
        m_ref   = luaL_ref(m_state, LUA_REGISTRYINDEX);
    }
}

luaref::luaref(luaref && r) {
    m_state = r.m_state;
    m_ref   = r.m_ref;
    r.m_state = nullptr;
}

luaref::~luaref() {
    if (m_state)
        luaL_unref(m_state, LUA_REGISTRYINDEX, m_ref);
}

void luaref::release() {
    if (m_state) {
        luaL_unref(m_state, LUA_REGISTRYINDEX, m_ref);
        m_state = nullptr;
    }
}

luaref & luaref::operator=(luaref const & r) {
    if (m_state != nullptr && r.m_state != nullptr && m_ref == r.m_ref)
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

void luaref::push() const {
    lean_assert(m_state);
    lua_rawgeti(m_state, LUA_REGISTRYINDEX, m_ref);
}

int luaref_lt_proc::operator()(luaref const & r1, luaref const & r2) const {
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
}
