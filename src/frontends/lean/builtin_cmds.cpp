/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
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
#include "library/reducible.h"
#include "library/normalize.h"
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
#include "frontends/lean/tokens.h"
#include "frontends/lean/pp_options.h"

namespace lean {
static void print_coercions(parser & p, optional<name> const & C) {
    environment const & env = p.env();
    options opts = p.regular_stream().get_options();
    opts = opts.update(get_pp_coercions_option_name(), true);
    io_state_stream out = p.regular_stream().update_options(opts);
    char const * arrow = get_pp_unicode(opts) ? "↣" : ">->";
    for_each_coercion_user(env, [&](name const & C1, name const & D, expr const & c, level_param_names const &, unsigned) {
            if (!C || *C == C1)
                out << C1 << " " << arrow << " " << D << " : " << c << endl;
        });
    for_each_coercion_sort(env, [&](name const & C1, expr const & c, level_param_names const &, unsigned) {
            if (!C || *C == C1)
                out << C1 << " " << arrow << " [sort-class] : " << c << endl;
        });
    for_each_coercion_fun(env, [&](name const & C1, expr const & c, level_param_names const &, unsigned) {
            if (!C || *C == C1)
                out << C1 << " " << arrow << " [fun-class] : " << c << endl;
        });
}

environment print_cmd(parser & p) {
    if (p.curr() == scanner::token_kind::String) {
        p.regular_stream() << p.get_str_val() << endl;
        p.next();
    } else if (p.curr_is_token_or_id(get_raw_tk())) {
        p.next();
        expr e = p.parse_expr();
        io_state_stream out = p.regular_stream();
        options opts = out.get_options();
        opts = opts.update(get_pp_notation_option_name(), false);
        out.update_options(opts) << e << endl;
    } else if (p.curr_is_token_or_id(get_options_tk())) {
        p.next();
        p.regular_stream() << p.ios().get_options() << endl;
    } else if (p.curr_is_token_or_id(get_definition_tk())) {
        p.next();
        auto pos = p.pos();
        name c = p.check_constant_next("invalid 'print definition', constant expected");
        environment const & env = p.env();
        declaration d = env.get(c);
        if (!d.is_definition())
            throw parser_error(sstream() << "invalid 'print definition', '" << c << "' is not a definition", pos);
        p.regular_stream() << d.get_value() << endl;
    } else if (p.curr_is_token_or_id(get_instances_tk())) {
        p.next();
        name c = p.check_constant_next("invalid 'print instances', constant expected");
        environment const & env = p.env();
        for (name const & i : get_class_instances(env, c)) {
            p.regular_stream() << i << " : " << env.get(i).get_type() << endl;
        }
    } else if (p.curr_is_token_or_id(get_classes_tk())) {
        p.next();
        environment const & env = p.env();
        buffer<name> classes;
        get_classes(env, classes);
        std::sort(classes.begin(), classes.end());
        for (name const & c : classes) {
            p.regular_stream() << c << " : " << env.get(c).get_type() << endl;
        }
    } else if (p.curr_is_token_or_id(get_coercions_tk())) {
        p.next();
        optional<name> C;
        if (p.curr_is_identifier())
            C = p.check_constant_next("invalid 'print coercions', constant expected");
        print_coercions(p, C);
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
    bool save_options = true;
    p.push_local_scope(save_options);
    return push_scope(p.env(), p.ios(), scope_kind::Context, n);
}

environment namespace_cmd(parser & p) {
    auto pos = p.pos();
    name n = p.check_atomic_id_next("invalid namespace declaration, atomic identifier expected");
    if (is_root_namespace(n))
        throw parser_error(sstream() << "invalid namespace name, '" << n << "' is reserved", pos);
    p.push_local_scope();
    return push_scope(p.env(), p.ios(), scope_kind::Namespace, n);
}

static void redeclare_aliases(parser & p,
                              list<pair<name, level>> old_level_entries,
                              list<pair<name, expr>> old_entries) {
    environment const & env = p.env();
    if (!in_context(env))
        return;
    list<pair<name, expr>> new_entries = p.get_local_entries();
    buffer<pair<name, expr>> to_redeclare;
    name_set popped_locals;
    while (!is_eqp(old_entries, new_entries)) {
        pair<name, expr> entry = head(old_entries);
        if (is_local_ref(entry.second))
            to_redeclare.push_back(entry);
        else if (is_local(entry.second))
            popped_locals.insert(mlocal_name(entry.second));
        old_entries = tail(old_entries);
    }
    name_set popped_levels;
    list<pair<name, level>> new_level_entries = p.get_local_level_entries();
    while (!is_eqp(old_level_entries, new_level_entries)) {
        level const & l = head(old_level_entries).second;
        if (is_param(l))
            popped_levels.insert(param_id(l));
        old_level_entries = tail(old_level_entries);
    }

    for (auto const & entry : to_redeclare) {
        expr new_ref = update_local_ref(entry.second, popped_levels, popped_locals);
        if (!is_constant(new_ref))
            p.add_local_expr(entry.first, new_ref);
    }
}

environment end_scoped_cmd(parser & p) {
    list<pair<name, level>> level_entries = p.get_local_level_entries();
    list<pair<name, expr>> entries        = p.get_local_entries();
    p.pop_local_scope();
    if (p.curr_is_identifier()) {
        name n = p.check_atomic_id_next("invalid end of scope, atomic identifier expected");
        environment env = pop_scope(p.env(), n);
        redeclare_aliases(p, level_entries, entries);
        return env;
    } else {
        environment env = pop_scope(p.env());
        redeclare_aliases(p, level_entries, entries);
        return env;
    }
}

/** \brief Auxiliary function for check/eval */
static std::tuple<expr, level_param_names> parse_local_expr(parser & p) {
    expr e   = p.parse_expr();
    environment const & env = p.env();
    if (is_constant(e) && !const_levels(e)) {
        // manually elaborate simple constant using nicer names for meta-variables
        if (auto decl = env.find(const_name(e))) {
            levels ls = param_names_to_levels(decl->get_univ_params());
            e         = mk_constant(const_name(e), ls);
            expr type = instantiate_type_univ_params(*decl, ls);
            while (true) {
                if (!is_pi(type))
                    break;
                if (is_explicit(binding_info(type)))
                    break;
                std::string q("?");
                q += binding_name(type).to_string();
                expr m = mk_local(name(q.c_str()), binding_domain(type));
                type   = instantiate(binding_body(type), m);
                e      = mk_app(e, m);
            }
            return std::make_tuple(e, decl->get_univ_params());
        }
    }
    list<expr> ctx = p.locals_to_context();
    level_param_names new_ls;
    std::tie(e, new_ls) = p.elaborate_relaxed(e, ctx);
    level_param_names ls = to_level_param_names(collect_univ_params(e));
    return std::make_tuple(e, ls);
}

environment check_cmd(parser & p) {
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);
    auto tc = mk_type_checker(p.env(), p.mk_ngen(), true);
    expr type = tc->check(e, ls).first;
    auto reg              = p.regular_stream();
    formatter const & fmt = reg.get_formatter();
    options opts          = p.ios().get_options();
    unsigned indent       = get_pp_indent(opts);
    format r = group(fmt(e) + space() + colon() + nest(indent, line() + fmt(type)));
    reg << mk_pair(r, opts) << endl;
    return p.env();
}

environment eval_cmd(parser & p) {
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);
    expr r = normalize(p.env(), ls, e);
    p.regular_stream() << r << endl;
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
            throw parser_error(sstream() << "unknown option '" << id
                               << "', type 'help options.' for list of available options", id_pos);
        } else {
            id = lean_id;
        }
    }
    option_kind k = decl_it->second.kind();
    if (k == BoolOption) {
        if (p.curr_is_token_or_id(get_true_tk()))
            p.set_option(id, true);
        else if (p.curr_is_token_or_id(get_false_tk()))
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
    if (p.curr_is_token(get_lbracket_tk())) {
        p.next();
        name n;
        if (p.curr_is_identifier())
            n = p.get_name_val();
        else if (p.curr_is_keyword() || p.curr_is_command())
            n = p.get_token_info().value();
        else
            throw parser_error("invalid 'open' command, identifier or symbol expected", p.pos());
        p.next();
        p.check_token_next(get_rbracket_tk(), "invalid 'open' command, ']' expected");
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
        bool decls = cls.is_anonymous() || cls == get_decls_tk() || cls == get_declarations_tk();
        auto pos   = p.pos();
        name ns    = p.check_id_next("invalid 'open/export' command, identifier expected");
        optional<name> real_ns = to_valid_namespace_name(env, ns);
        if (!real_ns)
            throw parser_error(sstream() << "invalid namespace name '" << ns << "'", pos);
        ns = *real_ns;
        name as;
        if (p.curr_is_token_or_id(get_as_tk())) {
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
            while (p.curr_is_token(get_lparen_tk())) {
                p.next();
                if (p.curr_is_token_or_id(get_renaming_tk())) {
                    p.next();
                    while (p.curr_is_identifier()) {
                        name from_id = p.get_name_val();
                        p.next();
                        p.check_token_next(get_arrow_tk(), "invalid 'open/export' command renaming, '->' expected");
                        name to_id = p.check_id_next("invalid 'open/export' command renaming, identifier expected");
                        check_identifier(p, env, ns, from_id);
                        exceptions.push_back(from_id);
                        if (open)
                            env = add_expr_alias(env, as+to_id, ns+from_id);
                        else
                            env = add_abbrev(p, env, as+to_id, ns+from_id);
                    }
                } else if (p.curr_is_token_or_id(get_hiding_tk())) {
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
                    throw parser_error("invalid 'open/export' command option, "
                                       "identifier, 'hiding' or 'renaming' expected", p.pos());
                }
                if (found_explicit && !exceptions.empty())
                    throw parser_error("invalid 'open/export' command option, "
                                       "mixing explicit and implicit 'open/export' options", p.pos());
                p.check_token_next(get_rparen_tk(), "invalid 'open/export' command option, ')' expected");
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
        if (!p.curr_is_token(get_lbracket_tk()) && !p.curr_is_identifier())
            break;
    }
    return env;
}
environment open_cmd(parser & p) { return open_export_cmd(p, true); }
environment export_cmd(parser & p) { return open_export_cmd(p, false); }

environment coercion_cmd(parser & p) {
    if (in_context(p.env()))
        throw parser_error("invalid 'coercion' command, coercions cannot be defined in contexts", p.pos());
    bool persistent = false;
    parse_persistent(p, persistent);
    name f   = p.check_constant_next("invalid 'coercion' command, constant expected");
    if (p.curr_is_token(get_colon_tk())) {
        p.next();
        name C = p.check_constant_next("invalid 'coercion' command, constant expected");
        return add_coercion(p.env(), f, C, p.ios(), persistent);
    } else {
        return add_coercion(p.env(), f, p.ios(), persistent);
    }
}

static void parse_reducible_modifiers(parser & p, reducible_status & status, bool & persistent) {
    while (true) {
        if (parse_persistent(p, persistent)) {
        } else if (p.curr_is_token_or_id(get_on_tk())) {
            p.next();
            status = reducible_status::On;
        } else if (p.curr_is_token_or_id(get_off_tk())) {
            p.next();
            status = reducible_status::Off;
        } else if (p.curr_is_token_or_id(get_none_tk())) {
            p.next();
            status = reducible_status::None;
        } else {
            break;
        }
    }
}

environment reducible_cmd(parser & p) {
    environment env         = p.env();
    reducible_status status = reducible_status::On;
    bool persistent         = false;
    parse_reducible_modifiers(p, status, persistent);
    bool found = false;
    while (p.curr_is_identifier()) {
        name c = p.check_constant_next("invalid 'reducible' command, constant expected");
        found   = true;
        env = set_reducible(env, c, status, persistent);
    }
    if (!found)
        throw exception("invalid empty 'reducible' command");
    return env;
}

environment irreducible_cmd(parser & p) {
    environment env         = p.env();
    reducible_status status = reducible_status::Off;
    bool persistent         = false;
    parse_persistent(p, persistent);
    bool found = false;
    while (p.curr_is_identifier()) {
        name c = p.check_constant_next("invalid 'irreducible' command, constant expected");
        found   = true;
        env = set_reducible(env, c, status, persistent);
    }
    if (!found)
        throw exception("invalid empty 'irreducible' command");
    return env;
}

environment erase_cache_cmd(parser & p) {
    name n = p.check_id_next("invalid #erase_cache command, identifier expected");
    p.erase_cached_definition(n);
    return p.env();
}

void init_cmd_table(cmd_table & r) {
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
    add_cmd(r, cmd_info("eval",         "evaluate given expression", eval_cmd));
    add_cmd(r, cmd_info("coercion",     "add a new coercion", coercion_cmd));
    add_cmd(r, cmd_info("reducible",    "mark definitions as reducible/irreducible for automation", reducible_cmd));
    add_cmd(r, cmd_info("irreducible",  "mark definitions as irreducible for automation", irreducible_cmd));
    add_cmd(r, cmd_info("#erase_cache", "erase cached definition (for debugging purposes)", erase_cache_cmd));

    register_decl_cmds(r);
    register_inductive_cmd(r);
    register_structure_cmd(r);
    register_notation_cmds(r);
    register_calc_cmds(r);
    register_begin_end_cmds(r);
    register_class_cmds(r);
    register_tactic_hint_cmd(r);
}

static cmd_table * g_cmds = nullptr;

cmd_table get_builtin_cmds() {
    return *g_cmds;
}

void initialize_builtin_cmds() {
    g_cmds = new cmd_table();
    init_cmd_table(*g_cmds);
}

void finalize_builtin_cmds() {
    delete g_cmds;
}
}
