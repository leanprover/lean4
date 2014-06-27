/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "util/script_state.h"
#include "util/luaref.h"
#include "library/kernel_bindings.h"
#include "library/tactic/cex_builder.h"

namespace lean {
cex_builder_fn mk_cex_builder_for(name const & gname) {
    return cex_builder_fn([=](name const & n, optional<counterexample> const & cex, substitution const &) -> counterexample {
            if (n != gname || !cex)
                throw exception(sstream() << "failed to build counterexample for '" << gname << "' goal");
            return *cex;
        });
}

cex_builder_fn to_cex_builder(lua_State * L, int idx) {
    luaL_checktype(L, idx, LUA_TFUNCTION); // user-fun
    luaref f(L, idx);
    return cex_builder_fn([=](name const & n, optional<counterexample> const & cex, substitution const & s) {
            lua_State * L = f.get_state();
            f.push();
            push_name(L, n);
            if (cex)
                push_environment(L, *cex);
            else
                lua_pushnil(L);
            push_substitution(L, s);
            pcall(L, 3, 1, 0);
            environment r = to_environment(L, -1);
            lua_pop(L, 1);
            return r;
        });
}
}
