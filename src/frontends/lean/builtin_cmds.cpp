/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/io_state_stream.h"
#include "frontends/lean/parser.h"

namespace lean {
static name g_raw("raw");

environment universe_cmd(parser & p) {
    if (p.curr_is_identifier()) {
        // TODO(Leo): take namespace and scopes into account
        name n = p.get_name_val();
        p.next();
        return p.env().add_global_level(n);
    } else {
        throw parser_error("invalid universe declaration, identifier expected", p.cmd_pos());
    }
}

environment print_cmd(parser & p) {
    if (p.curr() == scanner::token_kind::String) {
        p.regular_stream() << p.get_str_val() << "\n";
        p.next();
    } else if (p.curr_is_token(g_raw)) {
        p.next();
        expr e = p.parse_expr();
        p.regular_stream() << e << "\n";
    } else {
        throw parser_error("invalid print command", p.pos());
    }
    return p.env();
}

cmd_table init_cmd_table() {
    cmd_table r;
    add_cmd(r, cmd_info("print",    "print a string", print_cmd));
    add_cmd(r, cmd_info("universe", "declare a global universe level", universe_cmd));
    return r;
}

cmd_table get_builtin_cmds() {
    static optional<cmd_table> r;
    if (!r)
        r = init_cmd_table();
    return *r;
}
}
