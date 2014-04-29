/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/list.h"

namespace lean {
/** \brief Convert a Lua table into a list<T> */
template<typename T, typename Proc>
list<T> table_to_list(lua_State * L, int idx, Proc const & to_value) {
    if (lua_istable(L, idx)) {
        int n = objlen(L, idx);
        list<T> r;
        for (int i = n; i >= 1; i--) {
            lua_rawgeti(L, idx, i);
            r = cons(to_value(L, -1), r);
            lua_pop(L, 1);
        }
        return r;
    } else {
        throw exception("invalid argument, lua table expected");
    }
}
}
