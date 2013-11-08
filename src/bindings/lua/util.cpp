/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifdef LEAN_USE_LUA
#include <lua.hpp>
#include <exception>
#include <string>
#include "util/exception.h"
#include "util/debug.h"

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

size_t objlen(lua_State * L, int idx) {
    #ifdef LEAN_USE_LUA_OBJLEN
    return lua_objlen(L, idx);
    #else
    return lua_rawlen(L, idx);
    #endif
}

int safe_function_wrapper(lua_State * L, lua_CFunction f){
    static thread_local std::string _error_msg;
    char const * error_msg;
    try {
        return f(L);
    } catch (exception & e) {
        _error_msg = e.what();
        error_msg  = _error_msg.c_str();
    } catch (std::bad_alloc &) {
        error_msg = "out of memory";
    } catch (std::exception & e) {
        _error_msg = e.what();
        error_msg  = _error_msg.c_str();
    } catch(...) {
        throw;
    }
    return luaL_error(L, error_msg);
}
}
#endif
