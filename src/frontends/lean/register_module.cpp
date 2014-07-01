/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include "util/lua.h"
#include "util/script_state.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/parse_table.h"
#include "frontends/lean/parser_bindings.h"

namespace lean {

void open_frontend_lean(lua_State * L) {
    open_token_table(L);
    open_parse_table(L);
    open_parser(L);
}
void register_frontend_lean_module() {
    script_state::register_module(open_frontend_lean);
}
}
