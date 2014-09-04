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
#include "kernel/instantiate.h"
#include "library/io_state_stream.h"
#include "library/scoped_ext.h"
#include "library/aliases.h"
#include "library/protected.h"
#include "library/locals.h"
#include "library/coercion.h"
#include "library/opaque_hints.h"
#include "frontends/lean/util.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/calc.h"
#include "frontends/lean/notation_cmd.h"
#include "frontends/lean/inductive_cmd.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/begin_end_ext.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/class.h"
#include "frontends/lean/tactic_hint.h"

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
static name g_as("as");
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
    name n;
    if (p.curr_is_identifier())
        n = p.check_atomic_id_next("invalid section, atomic identifier expected");
    p.push_local_scope();
    return push_scope(p.env(), p.ios(), scope_kind::Section, n);
}

environment context_cmd(parser & p) {
    name n;
    if (p.curr_is_identifier())
        n = p.check_atomic_id_next("invalid context, atomic identifier expected");
    p.push_local_scope();
    return push_scope(p.env(), p.ios(), scope_kind::Context, n);
}

environment namespace_cmd(parser & p) {
    auto pos = p.pos();
    name n = p.check_atomic_id_next("invalid namespace declaration, atomic identifier expected");
    if (is_root_namespace(n))
        throw parser_error(sstream() << "invalid namespace name, '" << n << "' is reserved", pos);
    return push_scope(p.env(), p.ios(), scope_kind::Namespace, n);
}

environment end_scoped_cmd(parser & p) {
    if (in_section_or_context(p.env()))
        p.pop_local_scope();
    if (p.curr_is_identifier()) {
        name n = p.check_atomic_id_next("invalid end of scope, atomic identifier expected");
        return pop_scope(p.env(), n);
    } else {
        return pop_scope(p.env());
    }
}

environment check_cmd(parser & p) {
    expr e   = p.parse_expr();
    list<expr> ctx = locals_to_context(e, p);
    level_param_names ls = to_level_param_names(collect_univ_params(e));
    level_param_names new_ls;
    std::tie(e, new_ls) = p.elaborate_relaxed(e, ctx);
    auto tc = mk_type_checker_with_hints(p.env(), p.mk_ngen(), true);
    expr type = tc->check(e, append(ls, new_ls)).first;
    auto reg              = p.regular_stream();
    formatter const & fmt = reg.get_formatter();
    options opts          = p.ios().get_options();
    unsigned indent       = get_pp_indent(opts);
    format r = group(fmt(e) + space() + colon() + nest(indent, line() + fmt(type)));
    reg << mk_pair(r, opts) << endl;
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
            throw parser_error("invalid 'open' command, identifier or symbol expected", p.pos());
        p.next();
        p.check_token_next(g_rbracket, "invalid 'open' command, ']' expected");
        return n;
    } else {
        return name();
    }
}

static void check_identifier(parser & p, environment const & env, name const & ns, name const & id) {
    name full_id = ns + id;
    if (!env.find(full_id))
        throw parser_error(sstream() << "invalid 'open' command, unknown declaration '" << full_id << "'", p.pos());
}

// add id as an abbreviation for d
static environment add_abbrev(parser & p, environment const & env, name const & id, name const & d) {
    declaration decl = env.get(d);
    buffer<level> ls;
    for (name const & l : decl.get_univ_params())
        ls.push_back(mk_param_univ(l));
    expr value  = mk_constant(d, to_list(ls.begin(), ls.end()));
    bool opaque = false;
    name const & ns = get_namespace(env);
    name full_id    = ns + id;
    p.add_abbrev_index(full_id, d);
    environment new_env = module::add(env, check(env, mk_definition(env, full_id, decl.get_univ_params(), decl.get_type(), value, opaque)));
    if (full_id != id)
        new_env = add_expr_alias_rec(new_env, id, full_id);
    return new_env;
}

// open/export [class] id (as id)? (id ...) (renaming id->id id->id) (hiding id ... id)
environment open_export_cmd(parser & p, bool open) {
    environment env = p.env();
    while (true) {
        name cls = parse_class(p);
        bool decls = cls.is_anonymous() || cls == g_decls || cls == g_declarations;
        auto pos   = p.pos();
        name ns    = p.check_id_next("invalid 'open/export' command, identifier expected");
        optional<name> real_ns = to_valid_namespace_name(env, ns);
        if (!real_ns)
            throw parser_error(sstream() << "invalid namespace name '" << ns << "'", pos);
        ns = *real_ns;
        name as;
        if (p.curr_is_token_or_id(g_as)) {
            p.next();
            as = p.check_id_next("invalid 'open/export' command, identifier expected");
        }
        if (open)
            env = using_namespace(env, p.ios(), ns, cls);
        else
            env = export_namespace(env, p.ios(), ns, cls);
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
                        p.check_token_next(g_arrow, "invalid 'open/export' command renaming, '->' expected");
                        name to_id = p.check_id_next("invalid 'open/export' command renaming, identifier expected");
                        check_identifier(p, env, ns, from_id);
                        exceptions.push_back(from_id);
                        if (open)
                            env = add_expr_alias(env, as+to_id, ns+from_id);
                        else
                            env = add_abbrev(p, env, as+to_id, ns+from_id);
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
                        if (open)
                            env = add_expr_alias(env, as+id, ns+id);
                        else
                            env = add_abbrev(p, env, as+id, ns+id);
                    }
                } else {
                    throw parser_error("invalid 'open/export' command option, identifier, 'hiding' or 'renaming' expected", p.pos());
                }
                if (found_explicit && !exceptions.empty())
                    throw parser_error("invalid 'open/export' command option, mixing explicit and implicit 'open/export' options", p.pos());
                p.check_token_next(g_rparen, "invalid 'open/export' command option, ')' expected");
            }
            if (!found_explicit) {
                if (open) {
                    env = add_aliases(env, ns, as, exceptions.size(), exceptions.data());
                } else {
                    environment new_env = env;
                    env.for_each_declaration([&](declaration const & d) {
                            if (!is_protected(env, d.get_name()) &&
                                is_prefix_of(ns, d.get_name()) &&
                                !is_exception(d.get_name(), ns, exceptions.size(), exceptions.data())) {
                                name new_id = d.get_name().replace_prefix(ns, as);
                                if (!new_id.is_anonymous())
                                    new_env = add_abbrev(p, new_env, new_id, d.get_name());
                            }
                        });
                    env = new_env;
                }
            }
        }
        if (!p.curr_is_token(g_lbracket) && !p.curr_is_identifier())
            break;
    }
    return env;
}
environment open_cmd(parser & p) { return open_export_cmd(p, true); }
environment export_cmd(parser & p) { return open_export_cmd(p, false); }

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
                env = set_hide_main_opaque(env, hiding);
            } else {
                name c  = p.check_constant_next("invalid 'opaque_hint', constant expected");
                found   = true;
                if (hiding)
                    env = hide_definition(env, c);
                else
                    env = expose_definition(env, c);
            }
        }
        p.next();
    }
    if (!found)
        throw exception("invalid empty 'opaque_hint' command");
    return env;
}

environment erase_cache_cmd(parser & p) {
    name n = p.check_id_next("invalid #erase_cache command, identifier expected");
    p.erase_cached_definition(n);
    return p.env();
}

cmd_table init_cmd_table() {
    cmd_table r;
    add_cmd(r, cmd_info("open",         "create aliases for declarations, and use objects defined in other namespaces", open_cmd));
    add_cmd(r, cmd_info("export",       "create abbreviations for declarations, and export objects defined in other namespaces", export_cmd));
    add_cmd(r, cmd_info("set_option",   "set configuration option", set_option_cmd));
    add_cmd(r, cmd_info("exit",         "exit", exit_cmd));
    add_cmd(r, cmd_info("print",        "print a string", print_cmd));
    add_cmd(r, cmd_info("section",      "open a new section", section_cmd));
    add_cmd(r, cmd_info("context",      "open a new context", context_cmd));
    add_cmd(r, cmd_info("namespace",    "open a new namespace", namespace_cmd));
    add_cmd(r, cmd_info("end",          "close the current namespace/section", end_scoped_cmd));
    add_cmd(r, cmd_info("check",        "type check given expression, and display its type", check_cmd));
    add_cmd(r, cmd_info("coercion",     "add a new coercion", coercion_cmd));
    add_cmd(r, cmd_info("opaque_hint",  "add hints for the elaborator/unifier", opaque_hint_cmd));
    add_cmd(r, cmd_info("#erase_cache", "erase cached definition (for debugging purposes)", erase_cache_cmd));

    register_decl_cmds(r);
    register_inductive_cmd(r);
    register_structure_cmd(r);
    register_notation_cmds(r);
    register_calc_cmds(r);
    register_begin_end_cmds(r);
    register_class_cmds(r);
    register_tactic_hint_cmd(r);
    return r;
}

cmd_table get_builtin_cmds() {
    static optional<cmd_table> r;
    if (!r)
        r = init_cmd_table();
    return *r;
}
}
