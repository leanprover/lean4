/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/sstream.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "library/io_state_stream.h"
#include "library/scoped_ext.h"
#include "library/aliases.h"
#include "library/locals.h"
#include "library/coercion.h"
#include "library/opaque_hints.h"
#include "frontends/lean/util.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/calc.h"
#include "frontends/lean/notation_cmd.h"
#include "frontends/lean/inductive_cmd.h"
#include "frontends/lean/proof_qed_ext.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/class.h"

namespace lean {
static name g_raw("raw");
static name g_true("true");
static name g_false("false");
static name g_options("options");
static name g_lparen("(");
static name g_rparen(")");
static name g_arrow("->");
static name g_lbracket("[");
static name g_rbracket("]");
static name g_declarations("declarations");
static name g_decls("decls");
static name g_hiding("hiding");
static name g_exposing("exposing");
static name g_renaming("renaming");
static name g_module("[module]");
static name g_colon(":");

environment print_cmd(parser & p) {
    if (p.curr() == scanner::token_kind::String) {
        p.regular_stream() << p.get_str_val() << endl;
        p.next();
    } else if (p.curr_is_token_or_id(g_raw)) {
        p.next();
        expr e = p.parse_expr();
        p.regular_stream() << e << endl;
    } else if (p.curr_is_token_or_id(g_options)) {
        p.next();
        p.regular_stream() << p.ios().get_options() << endl;
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
    name n = p.check_id_next("invalid namespace declaration, identifier expected");
    check_atomic(n);
    return push_scope(p.env(), p.ios(), n);
}

environment end_scoped_cmd(parser & p) {
    if (in_section(p.env()))
        p.pop_local_scope();
    return pop_scope(p.env());
}

environment check_cmd(parser & p) {
    expr e   = p.parse_expr();
    buffer<expr> section_ps;
    name_set locals = collect_locals(e);
    mk_section_params(collect_locals(e), p, section_ps);
    e = p.lambda_abstract(section_ps, e);
    level_param_names ls = to_level_param_names(collect_univ_params(e));
    level_param_names new_ls;
    std::tie(e, new_ls) = p.elaborate_relaxed(e);
    auto tc = mk_type_checker_with_hints(p.env(), p.mk_ngen());
    expr type = tc->check(e, append(ls, new_ls));
    p.regular_stream() << e << " : " << type << endl;
    return p.env();
}

environment set_line_cmd(parser & p) {
    if (!p.curr_is_numeral())
        throw parser_error("invalid #setline command, numeral expected", p.pos());
    unsigned r = p.get_small_nat();
    p.set_line(r);
    p.next();
    return p.env();
}

environment exit_cmd(parser &) {
    throw interrupt_parser();
}

environment set_option_cmd(parser & p) {
    auto id_pos = p.pos();
    name id = p.check_id_next("invalid set option, identifier (i.e., option name) expected");
    auto decl_it = get_option_declarations().find(id);
    if (decl_it == get_option_declarations().end()) {
        // add "lean" prefix
        name lean_id = name("lean") + id;
        decl_it = get_option_declarations().find(lean_id);
        if (decl_it == get_option_declarations().end()) {
            throw parser_error(sstream() << "unknown option '" << id << "', type 'help options.' for list of available options", id_pos);
        } else {
            id = lean_id;
        }
    }
    option_kind k = decl_it->second.kind();
    if (k == BoolOption) {
        if (p.curr_is_token_or_id(g_true))
            p.set_option(id, true);
        else if (p.curr_is_token_or_id(g_false))
            p.set_option(id, false);
        else
            throw parser_error("invalid Boolean option value, 'true' or 'false' expected", p.pos());
        p.next();
    } else if (k == StringOption) {
        if (!p.curr_is_string())
            throw parser_error("invalid option value, given option is not a string", p.pos());
        p.set_option(id, p.get_str_val());
        p.next();
    } else if (k == DoubleOption) {
        p.set_option(id, p.parse_double());
    } else if (k == UnsignedOption || k == IntOption) {
        p.set_option(id, p.parse_small_nat());
    } else {
        throw parser_error("invalid option value, 'true', 'false', string, integer or decimal value expected", p.pos());
    }
    p.updt_options();
    return p.env();
}

static name parse_class(parser & p) {
    if (p.curr_is_token(g_lbracket)) {
        p.next();
        name n;
        if (p.curr_is_identifier())
            n = p.get_name_val();
        else if (p.curr_is_keyword() || p.curr_is_command())
            n = p.get_token_info().value();
        else
            throw parser_error("invalid 'using' command, identifier or symbol expected", p.pos());
        p.next();
        p.check_token_next(g_rbracket, "invalid 'using' command, ']' expected");
        return n;
    } else {
        return name();
    }
}

static void check_identifier(parser & p, environment const & env, name const & ns, name const & id) {
    name full_id = ns + id;
    if (!env.find(full_id))
        throw parser_error(sstream() << "invalid 'using' command, unknown declaration '" << full_id << "'", p.pos());
}

// using [class] id (id ...) (renaming id->id id->id) (hiding id ... id)
environment using_cmd(parser & p) {
    environment env = p.env();
    while (true) {
        name cls = parse_class(p);
        bool decls = cls.is_anonymous() || cls == g_decls || cls == g_declarations;
        auto pos   = p.pos();
        name ns    = p.check_id_next("invalid 'using' command, identifier expected");
        optional<name> real_ns = to_valid_namespace_name(env, ns);
        if (!real_ns)
            throw parser_error(sstream() << "invalid namespace name '" << ns << "'", pos);
        ns = *real_ns;
        env = using_namespace(env, p.ios(), ns, cls);
        if (decls) {
            // Remark: we currently to not allow renaming and hiding of universe levels
            buffer<name> exceptions;
            bool found_explicit = false;
            while (p.curr_is_token(g_lparen)) {
                p.next();
                if (p.curr_is_token_or_id(g_renaming)) {
                    p.next();
                    while (p.curr_is_identifier()) {
                        name from_id = p.get_name_val();
                        p.next();
                        p.check_token_next(g_arrow, "invalid 'using' command renaming, '->' expected");
                        name to_id = p.check_id_next("invalid 'using' command renaming, identifier expected");
                        check_identifier(p, env, ns, from_id);
                        exceptions.push_back(from_id);
                        env = add_alias(env, to_id, mk_constant(ns+from_id));
                    }
                } else if (p.curr_is_token_or_id(g_hiding)) {
                    p.next();
                    while (p.curr_is_identifier()) {
                        name id = p.get_name_val();
                        p.next();
                        check_identifier(p, env, ns, id);
                        exceptions.push_back(id);
                    }
                } else if (p.curr_is_identifier()) {
                    found_explicit = true;
                    while (p.curr_is_identifier()) {
                        name id = p.get_name_val();
                        p.next();
                        check_identifier(p, env, ns, id);
                        env = add_alias(env, id, mk_constant(ns+id));
                    }
                } else {
                    throw parser_error("invalid 'using' command option, identifier, 'hiding' or 'renaming' expected", p.pos());
                }
                if (found_explicit && !exceptions.empty())
                    throw parser_error("invalid 'using' command option, mixing explicit and implicit 'using' options", p.pos());
                p.check_token_next(g_rparen, "invalid 'using' command option, ')' expected");
            }
            if (!found_explicit)
                env = add_aliases(env, ns, name(), exceptions.size(), exceptions.data());
        }
        if (!p.curr_is_token(g_lbracket) && !p.curr_is_identifier())
            break;
    }
    return env;
}

environment coercion_cmd(parser & p) {
    auto pos = p.pos();
    expr f   = p.parse_expr();
    if (!is_constant(f))
        throw parser_error("invalid 'coercion' command, constant expected", pos);
    if (p.curr_is_token(g_colon)) {
        p.next();
        pos = p.pos();
        expr C = p.parse_expr();
        if (!is_constant(C))
            throw parser_error("invalid 'coercion' command, constant expected", pos);
        return add_coercion(p.env(), const_name(f), const_name(C), p.ios());
    } else {
        return add_coercion(p.env(), const_name(f), p.ios());
    }
}

environment opaque_hint_cmd(parser & p) {
    environment env = p.env();
    bool found = false;
    while (p.curr_is_token(g_lparen)) {
        p.next();
        bool hiding;
        auto pos = p.pos();
        if (p.curr_is_token_or_id(g_hiding))
            hiding = true;
        else if (p.curr_is_token_or_id(g_exposing))
            hiding = false;
        else
            throw parser_error("invalid 'opaque_hint', 'hiding' or 'exposing' expected", pos);
        p.next();
        while (!p.curr_is_token(g_rparen)) {
            if (p.curr_is_token(g_module)) {
                found = true;
                p.next();
                env = set_main_module_opaque_defs(env, hiding);
            } else {
                auto pos = p.pos();
                name id  = p.check_id_next("invalid 'opaque_hint', identifier expected");
                found    = true;
                expr e   = p.id_to_expr(id, pos);
                if (!is_constant(e))
                    throw parser_error(sstream() << "'" << id << "' is not a constant", pos);
                if (hiding)
                    env = hide_definition(env, const_name(e));
                else
                    env = expose_definition(env, const_name(e));
            }
        }
        p.next();
    }
    if (!found)
        throw exception("invalid empty 'opaque_hint' command");
    return env;
}

cmd_table init_cmd_table() {
    cmd_table r;
    add_cmd(r, cmd_info("using",        "create aliases for declarations, and use objects defined in other namespaces", using_cmd));
    add_cmd(r, cmd_info("set_option",   "set configuration option", set_option_cmd));
    add_cmd(r, cmd_info("exit",         "exit", exit_cmd));
    add_cmd(r, cmd_info("print",        "print a string", print_cmd));
    add_cmd(r, cmd_info("section",      "open a new section", section_cmd));
    add_cmd(r, cmd_info("namespace",    "open a new namespace", namespace_cmd));
    add_cmd(r, cmd_info("end",          "close the current namespace/section", end_scoped_cmd));
    add_cmd(r, cmd_info("check",        "type check given expression, and display its type", check_cmd));
    add_cmd(r, cmd_info("coercion",     "add a new coercion", coercion_cmd));
    add_cmd(r, cmd_info("opaque_hint",  "add hints for the elaborator/unifier", opaque_hint_cmd));
    add_cmd(r, cmd_info("#setline",     "modify the current line number, it only affects error/report messages", set_line_cmd));
    register_decl_cmds(r);
    register_inductive_cmd(r);
    register_notation_cmds(r);
    register_calc_cmds(r);
    register_proof_qed_cmds(r);
    register_class_cmds(r);
    return r;
}

cmd_table get_builtin_cmds() {
    static optional<cmd_table> r;
    if (!r)
        r = init_cmd_table();
    return *r;
}
}
