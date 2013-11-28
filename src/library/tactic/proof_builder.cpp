/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/script_state.h"
#include "util/exception.h"
#include "util/sstream.h"
#include "util/luaref.h"
#include "library/kernel_bindings.h"
#include "library/tactic/proof_builder.h"

namespace lean {
expr find(proof_map const & m, name const & n) {
    expr * r = const_cast<proof_map&>(m).splay_find(n);
    if (r)
        return *r;
    throw exception(sstream() << "proof for goal '" << n << "' not found");
}

DECL_UDATA(proof_map)

static int mk_proof_map(lua_State * L) {
    return push_proof_map(L, proof_map());
}

static int proof_map_len(lua_State * L) {
    lua_pushinteger(L, to_proof_map(L, 1).size());
    return 1;
}

static int proof_map_find(lua_State * L) {
    return push_expr(L, find(to_proof_map(L, 1), to_name_ext(L, 2)));
}

static int proof_map_insert(lua_State * L) {
    to_proof_map(L, 1).insert(to_name_ext(L, 2), to_expr(L, 3));
    return 0;
}

static int proof_map_erase(lua_State * L) {
    to_proof_map(L, 1).erase(to_name_ext(L, 2));
    return 0;
}

static const struct luaL_Reg proof_map_m[] = {
    {"__gc",            proof_map_gc}, // never throws
    {"__len",           safe_function<proof_map_len>},
    {"size",            safe_function<proof_map_len>},
    {"find",            safe_function<proof_map_find>},
    {"insert",          safe_function<proof_map_insert>},
    {"erase",           safe_function<proof_map_erase>},
    {0, 0}
};

DECL_UDATA(assignment);

static int mk_assignment(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0)
        return push_assignment(L, assignment(metavar_env()));
    else
        return push_assignment(L, assignment(to_metavar_env(L, 1)));
}

static int assignment_call(lua_State * L) {
    return push_expr(L, to_assignment(L, 1)(to_name_ext(L, 2)));
}

static const struct luaL_Reg assignment_m[] = {
    {"__gc",            assignment_gc}, // never throws
    {"__call",          safe_function<assignment_call>},
    {0, 0}
};

DECL_UDATA(proof_builder);

static int mk_proof_builder(lua_State * L) {
    script_state S = to_script_state(L);
    luaL_checktype(L, 1, LUA_TFUNCTION); // user-fun
    luaref ref(L, 1);
    return push_proof_builder(L,
                              mk_proof_builder([=](proof_map const & m, assignment const & a) -> expr {
                                      expr r;
                                      script_state _S(S);
                                      _S.exec_protected([&]() {
                                              ref.push(); // push user-fun on the stack
                                              push_proof_map(L, m);
                                              push_assignment(L, a);
                                              pcall(L, 2, 1, 0);
                                              r = to_expr(L, -1);
                                              lua_pop(L, 1);
                                          });
                                      return r;
                                  }));
}

static int proof_builder_call(lua_State * L) {
    proof_builder pb = to_proof_builder(L, 1);
    proof_map m      = to_proof_map(L, 2);
    assignment a     = to_assignment(L, 3);
    expr r;
    script_state S   = to_script_state(L);
    S.exec_unprotected([&]() {
            r = pb(m, a);
        });
    return push_expr(L, r);
}

static const struct luaL_Reg proof_builder_m[] = {
    {"__gc",            proof_builder_gc}, // never throws
    {"__call",          safe_function<proof_builder_call>},
    {0, 0}
};

static void proof_map_migrate(lua_State * src, int i, lua_State * tgt) {
    push_proof_map(tgt, to_proof_map(src, i));
}

static void assignment_migrate(lua_State * src, int i, lua_State * tgt) {
    push_assignment(tgt, to_assignment(src, i));
}

static void proof_builder_migrate(lua_State * src, int i, lua_State * tgt) {
    push_proof_builder(tgt, to_proof_builder(src, i));
}

void open_proof_builder(lua_State * L) {
    luaL_newmetatable(L, proof_map_mt);
    set_migrate_fn_field(L, -1, proof_map_migrate);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, proof_map_m, 0);

    SET_GLOBAL_FUN(proof_map_pred, "is_proof_map");
    SET_GLOBAL_FUN(mk_proof_map, "proof_map");

    luaL_newmetatable(L, assignment_mt);
    set_migrate_fn_field(L, -1, assignment_migrate);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, assignment_m, 0);

    SET_GLOBAL_FUN(assignment_pred, "is_assignment");
    SET_GLOBAL_FUN(mk_assignment, "assignment");

    luaL_newmetatable(L, proof_builder_mt);
    set_migrate_fn_field(L, -1, proof_builder_migrate);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, proof_builder_m, 0);

    SET_GLOBAL_FUN(proof_builder_pred, "is_proof_builder");
    SET_GLOBAL_FUN(mk_proof_builder, "proof_builder");
}
}
