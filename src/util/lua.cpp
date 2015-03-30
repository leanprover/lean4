/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <string>
#include <sstream>
#include <vector>
#include <memory>
#include <cstring>
#include <limits>
#include "util/lua.h"
#include "util/script_exception.h"
#include "util/debug.h"
#include "util/sstream.h"

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
            return p != nullptr;
        }
    }
    return false;  // value is not a userdata with a metatable
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

char const * tostring(lua_State * L, int idx) {
    if (!luaL_callmeta(L, idx, "__tostring")) {  /* no metafield? */
        switch (lua_type(L, idx)) {
        case LUA_TNUMBER:
        case LUA_TSTRING:
            lua_pushvalue(L, idx);
            break;
        case LUA_TBOOLEAN:
            lua_pushstring(L, (lua_toboolean(L, idx) ? "true" : "false"));
            break;
        case LUA_TNIL:
            lua_pushliteral(L, "nil");
            break;
        default: {
            std::ostringstream strm;
            strm << lua_typename(L, idx) << ": " << lua_topointer(L, idx);
            lua_pushstring(L, strm.str().c_str());
            break;
        }}
    }
    return lua_tostring(L, -1);
}

int get_nonnil_top(lua_State * L) {
    int top = lua_gettop(L);
    while (top > 0 && lua_isnil(L, top))
        top--;
    return top;
}

static void exec(lua_State * L) {
    pcall(L, 0, LUA_MULTRET, 0);
}

void check_result(lua_State * L, int result) {
    if (result) {
        if (is_exception(L, -1)) {
            to_exception(L, -1).rethrow();
        } else {
            throw script_exception(lua_tostring(L, -1));
        }
    }
}

void dofile(lua_State * L, char const * fname) {
    int result = luaL_loadfile(L, fname);
    check_result(L, result);
    exec(L);
}

void dostring(lua_State * L, char const * str) {
    int result = luaL_loadstring(L, str);
    check_result(L, result);
    exec(L);
}

void pcall(lua_State * L, int nargs, int nresults, int errorfun) {
    int result = lua_pcall(L, nargs, nresults, errorfun);
    check_result(L, result);
}

bool resume(lua_State * L, int nargs) {
    #if LUA_VERSION_NUM < 502
    int result = lua_resume(L, nargs);
    #else
    int result = lua_resume(L, nullptr, nargs);
    #endif
    if (result == LUA_YIELD)
        return false;
    if (result == 0)
        return true;
    check_result(L, result);
    lean_unreachable();
    return true;
}

void throw_bad_arg_error(lua_State * L, int i, char const * expected_type) {
    lua_Debug ar;
    if (!lua_getstack(L, 0, &ar))  /* no stack frame? */
        throw exception(sstream() << "bad argument #" << i << " (" << expected_type << " expected)");
    lua_getinfo(L, "n", &ar);
    if (strcmp(ar.namewhat, "method") == 0 || ar.name == nullptr)
        throw exception(sstream() << "bad argument #" << i << " (" << expected_type << " expected)");
    throw exception(sstream() << "bad argument #" << i << " to '" << ar.name << "' (" << expected_type << " expected)");
}

/**
   \brief Wrapper for "customers" that are only using a subset
   of Lean libraries.
*/
int safe_function_wrapper(lua_State * L, lua_CFunction f) {
    try {
        return f(L);
    } catch (throwable & e) {
        lua_Debug ar;
        lua_getstack(L, 1, &ar);
        lua_getinfo(L, "Sl", &ar);
        if (ar.source && *(ar.source) == '@')
            push_exception(L, script_nested_exception(true, ar.source+1, ar.currentline,
                                                      std::shared_ptr<throwable>(e.clone())));
        else if (ar.source)
            push_exception(L, script_nested_exception(false, ar.source, ar.currentline,
                                                      std::shared_ptr<throwable>(e.clone())));
        else
            push_exception(L, e);
    } catch (std::bad_alloc &) {
        lua_pushstring(L, "out of memory");
    } catch (std::exception & e) {
        lua_pushstring(L, e.what());
    } catch(...) {
        lua_pushstring(L, "unknown error");
    }
    return lua_error(L);
}

void check_num_args(lua_State * L, int num) {
    if (lua_gettop(L) != num) throw exception("incorrect number of arguments to function");
}
void check_atmost_num_args(lua_State * L, int high) {
    if (lua_gettop(L) > high) throw exception("too many arguments to function");
}
void check_atleast_num_args(lua_State * L, int low) {
    if (lua_gettop(L) < low) throw exception("too few arguments to function");
}
}
