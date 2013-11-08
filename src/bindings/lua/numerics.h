/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <lua.hpp>
namespace lean {
class mpz;
void open_mpz(lua_State * L);
bool is_mpz(lua_State * L, int idx);
mpz & to_mpz(lua_State * L, int idx);
int push_mpz(lua_State * L, mpz const & val);

class mpq;
void open_mpq(lua_State * L);
bool is_mpq(lua_State * L, int idx);
mpq & to_mpq(lua_State * L, int idx);
int push_mpq(lua_State * L, mpq const & val);
}
