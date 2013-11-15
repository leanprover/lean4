/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>
namespace lean {
UDATA_DEFS(mpz)
mpz to_mpz_ext(lua_State * L, int idx);
void open_mpz(lua_State * L);

UDATA_DEFS(mpq)
mpq to_mpq_ext(lua_State * L, int idx);
void open_mpq(lua_State * L);
}
