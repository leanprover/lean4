/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifdef LEAN_USE_LUA
#include <sstream>
#include <lua.hpp>
#include "util/debug.h"
#include "util/numerics/mpz.h"
#include "util/numerics/mpq.h"

namespace lean {
template<typename T, char const * N, char const * M>
class num_bindings {
public:
    template<unsigned idx>
    static T const & get_arg(lua_State * L) {
        static thread_local T arg;
        if (lua_isuserdata(L, idx)) {
            return *static_cast<T*>(luaL_checkudata(L, idx, M));
        } else if (lua_isstring(L, idx)) {
            char const * str = luaL_checkstring(L, idx);
            arg = T(str);
            return arg;
        } else {
            arg = luaL_checkinteger(L, 1);
            return arg;
        }
    }

    static int push_result(lua_State * L, T const & val) {
        void * mem = lua_newuserdata(L, sizeof(T));
        new (mem) T(val);
        luaL_getmetatable(L, M);
        lua_setmetatable(L, -2);
        return 1;
    }

    static int gc(lua_State * L) {
        T * n = static_cast<T*>(luaL_checkudata(L, 1, M));
        n->~T();
        return 0;
    }

    static int tostring(lua_State * L) {
        T * n = static_cast<T*>(luaL_checkudata(L, 1, M));
        std::ostringstream out;
        out << *n;
        lua_pushfstring(L, out.str().c_str());
        return 1;
    }

    static int eq(lua_State * L) {
        lua_pushboolean(L, get_arg<1>(L) == get_arg<2>(L));
        return 1;
    }

    static int lt(lua_State * L) {
        lua_pushboolean(L, get_arg<1>(L) < get_arg<2>(L));
        return 1;
    }

    static int add(lua_State * L) {
        return push_result(L, get_arg<1>(L) + get_arg<2>(L));
    }

    static int sub(lua_State * L) {
        return push_result(L, get_arg<1>(L) - get_arg<2>(L));
    }

    static int mul(lua_State * L) {
        return push_result(L, get_arg<1>(L) * get_arg<2>(L));
    }

    static int div(lua_State * L) {
        T const & arg2 = get_arg<2>(L);
        if (arg2 == 0) luaL_error(L, "division by zero");
        return push_result(L, get_arg<1>(L) / arg2);
    }

    static int umn(lua_State * L) {
        return push_result(L, 0 - get_arg<1>(L));
    }

    static int power(lua_State * L) {
        int k = luaL_checkinteger(L, 2);
        if (k < 0) luaL_error(L, "argument #2 must be positive");
        return push_result(L, pow(get_arg<1>(L), k));
    }

    static const struct luaL_Reg m[];

    static int mk(lua_State * L) {
        T const & arg = get_arg<1>(L);
        return push_result(L, arg);
    }

    static void init(lua_State * L) {
        luaL_newmetatable(L, M);
        luaL_setfuncs(L, m, 0);

        lua_pushcfunction(L, mk);
        lua_setglobal(L, N);
    }
};

template<typename T, char const * N, char const * M>
const struct luaL_Reg num_bindings<T, N, M>::m[] = {
    {"__gc", num_bindings<T, N, M>::gc}, {"__tostring", num_bindings<T, N, M>::tostring}, {"__eq", num_bindings<T, N, M>::eq},
    {"__lt", num_bindings<T, N, M>::lt}, {"__add", num_bindings<T, N, M>::add}, {"__add", num_bindings<T, N, M>::sub},
    {"__mul", num_bindings<T, N, M>::mul}, {"__div", num_bindings<T, N, M>::div}, {"__pow", num_bindings<T, N, M>::power},
    {"__unm", num_bindings<T, N, M>::umn},
    {0, 0}
};

constexpr char const mpz_name[]      = "mpz";
constexpr char const mpz_metatable[] = "mpz.mt";
void init_mpz(lua_State * L) {
    num_bindings<mpz, mpz_name, mpz_metatable>::init(L);
}
constexpr char const mpq_name[]      = "mpq";
constexpr char const mpq_metatable[] = "mpq.mt";
void init_mpq(lua_State * L) {
    num_bindings<mpq, mpq_name, mpq_metatable>::init(L);
}
}
#endif
