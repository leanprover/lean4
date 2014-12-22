/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/num.h"
#include "library/normalize.h"
#include "library/class.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"

namespace lean {
optional<unsigned> parse_instance_priority(parser & p) {
    if (p.curr_is_token(get_priority_tk())) {
        p.next();
        auto pos = p.pos();
        environment env = open_priority_aliases(open_num_notation(p.env()));
        parser::local_scope scope(p, env);
        expr val = p.parse_expr();
        val = normalize(p.env(), val);
        if (optional<mpz> mpz_val = to_num(val)) {
            if (!mpz_val->is_unsigned_int())
                throw parser_error("invalid 'priority', argument does not fit in a machine integer", pos);
            p.check_token_next(get_rbracket_tk(), "invalid 'priority', ']' expected");
            return optional<unsigned>(mpz_val->get_unsigned_int());
        } else {
            throw parser_error("invalid 'priority', argument does not evaluate to a numeral", pos);
        }
    } else {
        return optional<unsigned>();
    }
}

environment add_instance_cmd(parser & p) {
    bool found = false;
    bool persistent = false;
    parse_persistent(p, persistent);
    optional<unsigned> priority = parse_instance_priority(p);
    environment env = p.env();
    while (p.curr_is_identifier()) {
        found    = true;
        name c   = p.check_constant_next("invalid 'class instance' declaration, constant expected");
        if (priority)
            env = add_instance(env, c, *priority, persistent);
        else
            env = add_instance(env, c, persistent);
    }
    if (!found)
        throw parser_error("invalid 'class instance' declaration, at least one identifier expected", p.pos());
    return env;
}


environment add_class_cmd(parser & p) {
    bool found = false;
    environment env = p.env();
    bool persistent = false;
    parse_persistent(p, persistent);
    while (p.curr_is_identifier()) {
        found    = true;
        name c   = p.check_constant_next("invalid 'class' declaration, constant expected");
        env = add_class(env, c, persistent);
    }
    if (!found)
        throw parser_error("invalid 'class' declaration, at least one identifier expected", p.pos());
    return env;
}

environment multiple_instances_cmd(parser & p) {
    bool found = false;
    environment env = p.env();
    bool persistent = false;
    parse_persistent(p, persistent);
    while (p.curr_is_identifier()) {
        found    = true;
        name c   = p.check_constant_next("invalid 'multiple_instances' command, constant expected");
        env = mark_multiple_instances(env, c, persistent);
    }
    if (!found)
        throw parser_error("invalid 'multiple_instances' command, at least one identifier expected", p.pos());
    return env;
}

void register_class_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("instance",           "add a new instance", add_instance_cmd));
    add_cmd(r, cmd_info("class",              "add a new class", add_class_cmd));
    add_cmd(r, cmd_info("multiple_instances", "mark that Lean must explore multiple instances of the given class", multiple_instances_cmd));
}
}
