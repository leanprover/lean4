/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/io_state_stream.h"
#include "frontends/lean/parser.h"

namespace lean {
environment print_cmd(parser & p) {
    if (p.curr() == scanner::token_kind::String) {
        regular(p.env(), p.ios()) << p.get_str_val() << "\n";
        p.next();
    } else {
        throw parser_error("invalid print command", p.pos());
    }
    return p.env();
}

cmd_table init_cmd_table() {
    cmd_table r;
    add_cmd(r, cmd_info("print", "print a string", print_cmd));
    return r;
}

cmd_table get_builtin_cmds() {
    static optional<cmd_table> r;
    if (!r)
        r = init_cmd_table();
    return *r;
}
}

