/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <lua.hpp>
#include <string>
#include <sstream>
#include "kernel/kernel_exception.h"
#include "library/elaborator/elaborator_exception.h"
#include "bindings/lua/util.h"
#include "bindings/lua/lua_exception.h"
#include "bindings/lua/options.h"
#include "bindings/lua/format.h"
#include "bindings/lua/formatter.h"
#include "bindings/lua/justification.h"

namespace lean {
/**
   \brief luaL_setfuncs replacement. The function luaL_setfuncs is only available in Lua 5.2.
*/
void setfuncs(lua_State * L, luaL_Reg const * l, int nup) {
    luaL_checkstack(L, nup, "too many upvalues");
    for (; l->name != NULL; l++) {
        // fill the table with given functions
        for (int i = 0; i < nup; i++) // copy upvalues to the top
            lua_pushvalue(L, -nup);
        lua_pushcclosure(L, l->func, nup);  // closure with those upvalues
        lua_setfield(L, -(nup + 2), l->name);
    }
    lua_pop(L, nup);  // remove upvalues
}

/**
   \brief luaL_testudata replacement.
*/
bool testudata(lua_State * L, int ud, char const * tname) {
    void * p = lua_touserdata(L, ud);
    if (p != nullptr) {
        if (lua_getmetatable(L, ud)) {
            luaL_getmetatable(L, tname);
            if (!lua_rawequal(L, -1, -2))
                p = nullptr;
            lua_pop(L, 2);
            return p;
        }
    }
    return nullptr;  // value is not a userdata with a metatable
}

int load(lua_State * L, lua_Reader reader, void * data, char const * source) {
    #if LUA_VERSION_NUM < 502
    return lua_load(L, reader, data, source);
    #else
    return lua_load(L, reader, data, source, nullptr);
    #endif
}

size_t objlen(lua_State * L, int idx) {
    #if LUA_VERSION_NUM < 502
    return lua_objlen(L, idx);
    #else
    return lua_rawlen(L, idx);
    #endif
}

int lessthan(lua_State * L, int idx1, int idx2) {
    #if LUA_VERSION_NUM < 502
    return lua_lessthan(L, idx1, idx2);
    #else
    return lua_compare(L, idx1, idx2, LUA_OPLT);
    #endif
}

int equal(lua_State * L, int idx1, int idx2) {
    #if LUA_VERSION_NUM < 502
    return lua_equal(L, idx1, idx2);
    #else
    return lua_compare(L, idx1, idx2, LUA_OPEQ);
    #endif
}

static void exec(lua_State * L) {
    pcall(L, 0, LUA_MULTRET, 0);
}

void dofile(lua_State * L, char const * fname) {
    int result = luaL_loadfile(L, fname);
    if (result)
        throw lua_exception(lua_tostring(L, -1));
    exec(L);
}

void dostring(lua_State * L, char const * str) {
    int result = luaL_loadstring(L, str);
    if (result)
        throw lua_exception(lua_tostring(L, -1));
    exec(L);
}

void pcall(lua_State * L, int nargs, int nresults, int errorfun) {
    int result = lua_pcall(L, nargs, nresults, errorfun);
    if (result)
        throw lua_exception(lua_tostring(L, -1));
}

static thread_local std::string g_error_msg;

int safe_function_wrapper(lua_State * L, lua_CFunction f){
    char const * error_msg;
    try {
        return f(L);
    } catch (kernel_exception & e) {
        std::ostringstream out;
        options o = get_global_options(L);
        out << mk_pair(e.pp(get_global_formatter(L), o), o);
        g_error_msg = out.str();
        error_msg  = g_error_msg.c_str();
    } catch (elaborator_exception & e) {
        push_justification(L, e.get_justification());
        return lua_error(L);
    } catch (exception & e) {
        g_error_msg = e.what();
        error_msg  = g_error_msg.c_str();
    } catch (std::bad_alloc &) {
        error_msg = "out of memory";
    } catch (std::exception & e) {
        g_error_msg = e.what();
        error_msg  = g_error_msg.c_str();
    } catch(...) {
        throw;
    }
    return luaL_error(L, error_msg);
}
}
