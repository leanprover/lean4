/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "library/io_state_stream.h"
#include "library/scoped_ext.h"
#include "library/aliases.h"
#include "frontends/lean/parser.h"

namespace lean {
static name g_raw("raw");
static void check_atomic(name const & n) {
    if (!n.is_atomic())
        throw exception(sstream() << "invalid declaration name '" << n << "', identifier must be atomic");
}

environment universe_cmd(parser & p) {
    if (p.curr_is_identifier()) {
        name n = p.get_name_val();
        check_atomic(n);
        p.next();
        environment env = p.env();
        if (in_section(env)) {
            p.add_local_level(n, mk_param_univ(n));
        } else {
            name const & ns = get_namespace(env);
            name full_n  = ns + n;
            env = env.add_universe(full_n);
            if (!ns.is_anonymous())
                env = add_alias(env, n, mk_global_univ(full_n));
        }
        return env;
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

environment section_cmd(parser & p) {
    p.push_local_scope();
    return push_scope(p.env(), p.ios());
}

environment namespace_cmd(parser & p) {
    if (p.curr_is_identifier()) {
        name n = p.get_name_val();
        check_atomic(n);
        p.next();
        return push_scope(p.env(), p.ios(), n);
    } else {
        throw parser_error("invalid namespace declaration, identifier expected", p.cmd_pos());
    }
}

environment end_scoped_cmd(parser & p) {
    if (in_section(p.env()))
        p.pop_local_scope();
    return pop_scope(p.env());
}

cmd_table init_cmd_table() {
    cmd_table r;
    add_cmd(r, cmd_info("print",     "print a string", print_cmd));
    add_cmd(r, cmd_info("universe",  "declare a global universe level", universe_cmd));
    add_cmd(r, cmd_info("section",   "open a new section", section_cmd));
    add_cmd(r, cmd_info("namespace", "open a new namespace", namespace_cmd));
    add_cmd(r, cmd_info("end",       "close the current namespace/section", end_scoped_cmd));
    return r;
}

cmd_table get_builtin_cmds() {
    static optional<cmd_table> r;
    if (!r)
        r = init_cmd_table();
    return *r;
}
}
