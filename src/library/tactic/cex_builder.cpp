/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/luaref.h"
#include "library/kernel_bindings.h"
#include "library/tactic/proof_builder.h"
#include "library/tactic/cex_builder.h"

namespace lean {
cex_builder & cex_builder::operator=(cex_builder const & s) { LEAN_COPY_REF(cex_builder, s); }
cex_builder & cex_builder::operator=(cex_builder && s) { LEAN_MOVE_REF(cex_builder, s); }

DECL_UDATA(cex_builder)

static int mk_cex_builder(lua_State * L) {
    luaL_checktype(L, 1, LUA_TFUNCTION); // user-fun
    luaref ref(L, 1);
    return push_cex_builder(L,
                            mk_cex_builder([=](name const & n, optional<counterexample> const & cex, assignment const & a) -> counterexample {
                                      ref.push(); // push user-fun on the stack
                                      push_name(L, n);
                                      if (cex)
                                          push_environment(L, *cex);
                                      else
                                          lua_pushnil(L);
                                      push_assignment(L, a);
                                      pcall(L, 3, 1, 0);
                                      environment r = to_environment(L, -1);
                                      lua_pop(L, 1);
                                      return r;
                                  }));
}

static int cex_builder_call(lua_State * L) {
    if (is_environment(L, 3))
        return push_environment(L, to_cex_builder(L, 1)(to_name_ext(L, 2), optional<counterexample>(to_environment(L, 3)), to_assignment(L, 4)));
    else
        return push_environment(L, to_cex_builder(L, 1)(to_name_ext(L, 2), optional<counterexample>(), to_assignment(L, 4)));
}

static const struct luaL_Reg cex_builder_m[] = {
    {"__gc",            cex_builder_gc}, // never throws
    {"__call",          safe_function<cex_builder_call>},
    {0, 0}
};

void open_cex_builder(lua_State * L) {
    luaL_newmetatable(L, cex_builder_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, cex_builder_m, 0);

    SET_GLOBAL_FUN(cex_builder_pred, "is_cex_builder");
    SET_GLOBAL_FUN(mk_cex_builder, "cex_builder");
}
}
