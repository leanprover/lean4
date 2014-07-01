/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "frontends/lean/parser.h"
namespace lean {
struct scoped_set_parser {
    lua_State * m_state;
    parser *    m_old;
    scoped_set_parser(lua_State * L, parser & p);
    ~scoped_set_parser();
};
void open_parser(lua_State * L);
}
