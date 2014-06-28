/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/exception.h"
#include "util/sstream.h"
#include "util/luaref.h"
#include "library/kernel_bindings.h"
#include "library/tactic/proof_builder.h"

namespace lean {
expr find(proof_map const & m, name const & n) {
    expr const * r = m.find(n);
    if (r)
        return *r;
    throw exception(sstream() << "proof for goal '" << n << "' not found");
}

proof_builder add_proofs(proof_builder const & pb, list<std::pair<name, expr>> const & prs) {
    return proof_builder([=](proof_map const & m, substitution const & s) -> expr {
            proof_map new_m(m);
            for (auto const & np : prs) {
                new_m.insert(np.first, np.second);
            }
            return pb(new_m, s);
        });
}

DECL_UDATA(proof_map)

static int mk_proof_map(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0)
        return push_proof_map(L, proof_map());
    else
        return push_proof_map(L, to_proof_map(L, 1));
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
    {"find",            safe_function<proof_map_find>},
    {"insert",          safe_function<proof_map_insert>},
    {"erase",           safe_function<proof_map_erase>},
    {0, 0}
};

proof_builder to_proof_builder(lua_State * L, int idx) {
    luaL_checktype(L, idx, LUA_TFUNCTION); // user-fun
    luaref f(L, idx);
    return proof_builder([=](proof_map const & m, substitution const & s) {
            lua_State * L = f.get_state();
            f.push();
            push_proof_map(L, m);
            push_substitution(L, s);
            pcall(L, 2, 1, 0);
            expr r = to_expr(L, -1);
            lua_pop(L, 1);
            return r;
        });
}

void open_proof_builder(lua_State * L) {
    luaL_newmetatable(L, proof_map_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, proof_map_m, 0);

    SET_GLOBAL_FUN(proof_map_pred, "is_proof_map");
    SET_GLOBAL_FUN(mk_proof_map, "proof_map");
}
}
