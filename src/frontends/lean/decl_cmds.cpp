/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/sstream.h"
#include "kernel/type_checker.h"
#include "library/scoped_ext.h"
#include "library/aliases.h"
#include "library/private.h"
#include "library/placeholder.h"
#include "library/locals.h"
#include "library/explicit.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"

namespace lean {
static name g_llevel_curly(".{");
static name g_lcurly("{");
static name g_rcurly("}");
static name g_lbracket("[");
static name g_rbracket("]");
static name g_colon(":");
static name g_assign(":=");
static name g_private("[private]");
static name g_inline("[inline]");

environment universe_cmd(parser & p) {
    name n = p.check_id_next("invalid universe declaration, identifier expected");
    check_atomic(n);
    environment env = p.env();
    if (in_section(env)) {
        p.add_local_level(n, mk_param_univ(n));
    } else {
        name const & ns = get_namespace(env);
        name full_n  = ns + n;
        env = module::add_universe(env, full_n);
        if (!ns.is_anonymous())
            env = add_alias(env, n, mk_global_univ(full_n));
    }
    return env;
}

binder_info parse_open_binder_info(parser & p) {
    if (p.curr_is_token(g_lcurly)) {
        check_in_section(p);
        p.next();
        return mk_implicit_binder_info();
    } else if (p.curr_is_token(g_lbracket)) {
        check_in_section(p);
        p.next();
        return mk_cast_binder_info();
    } else {
        return binder_info();
    }
}

void parse_close_binder_info(parser & p, binder_info const & bi) {
    if (bi.is_implicit()) {
        p.check_token_next(g_rcurly, "invalid declaration, '}' expected");
    } else if (bi.is_cast()) {
        p.check_token_next(g_rbracket, "invalid declaration, ']' expected");
    }
}

bool parse_univ_params(parser & p, buffer<name> & ps) {
    if (p.curr_is_token(g_llevel_curly)) {
        p.next();
        while (!p.curr_is_token(g_rcurly)) {
            name l = p.check_id_next("invalid universe parameter, identifier expected");
            p.add_local_level(l, mk_param_univ(l));
            ps.push_back(l);
        }
        p.next();
        return true;
    } else{
        return false;
    }
}

void update_univ_parameters(buffer<name> & ls_buffer, name_set const & found, parser const & p) {
    unsigned old_sz = ls_buffer.size();
    found.for_each([&](name const & n) {
            if (std::find(ls_buffer.begin(), ls_buffer.begin() + old_sz, n) == ls_buffer.begin() + old_sz)
                ls_buffer.push_back(n);
        });
    std::sort(ls_buffer.begin(), ls_buffer.end(), [&](name const & n1, name const & n2) {
            return p.get_local_level_index(n1) < p.get_local_level_index(n2);
        });
}

static environment declare_var(parser & p, environment env,
                               name const & n, level_param_names const & ls, expr const & type,
                               bool is_axiom, binder_info const & bi, pos_info const & pos) {
    if (in_section(p.env())) {
        p.add_local_expr(n, p.save_pos(mk_local(n, type), pos), bi);
        return env;
    } else {
        name const & ns = get_namespace(env);
        name full_n  = ns + n;
        if (is_axiom)
            env = module::add(env, check(env, mk_axiom(full_n, ls, type)));
        else
            env = module::add(env, check(env, mk_var_decl(full_n, ls, type)));
        if (!ns.is_anonymous())
            env = add_alias(env, n, mk_constant(full_n));
        return env;
    }
}

environment variable_cmd_core(parser & p, bool is_axiom) {
    auto pos = p.pos();
    binder_info bi = parse_open_binder_info(p);
    name n = p.check_id_next("invalid declaration, identifier expected");
    check_atomic(n);
    buffer<name> ls_buffer;
    if (p.curr_is_token(g_llevel_curly) && in_section(p.env()))
        throw parser_error("invalid declaration, axioms/parameters occurring in sections cannot be universe polymorphic", p.pos());
    optional<parser::local_scope> scope1;
    if (!in_section(p.env()))
        scope1.emplace(p);
    parse_univ_params(p, ls_buffer);
    parser::param_universe_scope scope2(p);
    expr type;
    if (!p.curr_is_token(g_colon)) {
        buffer<parameter> ps;
        auto lenv = p.parse_binders(ps);
        p.check_token_next(g_colon, "invalid declaration, ':' expected");
        type = p.parse_scoped_expr(ps, lenv);
        type = p.pi_abstract(ps, type);
    } else {
        p.next();
        type = p.parse_expr();
    }
    parse_close_binder_info(p, bi);
    level_param_names ls;
    if (in_section(p.env())) {
        ls = to_level_param_names(collect_univ_params(type));
    } else {
        update_univ_parameters(ls_buffer, collect_univ_params(type), p);
        ls = to_list(ls_buffer.begin(), ls_buffer.end());
    }
    type = p.elaborate(type);
    return declare_var(p, p.env(), n, ls, type, is_axiom, bi, pos);
}
environment variable_cmd(parser & p) {
    return variable_cmd_core(p, false);
}
environment axiom_cmd(parser & p)    {
    return variable_cmd_core(p, true);
}

// Sort local_names by order of occurrence in the section, and copy the associated parameters to section_ps
void mk_section_params(name_set const & local_names, parser const & p, buffer<parameter> & section_ps) {
    local_names.for_each([&](name const & n) {
            section_ps.push_back(*p.get_local(n));
        });
    std::sort(section_ps.begin(), section_ps.end(), [&](parameter const & p1, parameter const & p2) {
            return p.get_local_index(mlocal_name(p1.m_local)) < p.get_local_index(mlocal_name(p2.m_local));
        });
}

// Collect local (section) constants occurring in type and value, sort them, and store in section_ps
void collect_section_locals(expr const & type, expr const & value, parser const & p, buffer<parameter> & section_ps) {
    name_set ls = collect_locals(type, collect_locals(value));
    return mk_section_params(ls, p, section_ps);
}

static void parse_modifiers(parser & p, bool & is_private, bool & is_opaque) {
    while (true) {
        if (p.curr_is_token(g_private)) {
            is_private = true;
            p.next();
        } else if (p.curr_is_token(g_inline)) {
            is_opaque = false;
            p.next();
        } else {
            break;
        }
    }
}

// Return the levels in \c ls that are defined in the section
levels collect_section_levels(level_param_names const & ls, parser & p) {
    buffer<level> section_ls_buffer;
    for (name const & l : ls) {
        if (p.get_local_level_index(l))
            section_ls_buffer.push_back(mk_param_univ(l));
        else
            break;
    }
    return to_list(section_ls_buffer.begin(), section_ls_buffer.end());
}

environment definition_cmd_core(parser & p, bool is_theorem, bool is_opaque) {
    name n = p.check_id_next("invalid declaration, identifier expected");
    check_atomic(n);
    bool is_private = false;
    parse_modifiers(p, is_private, is_opaque);
    if (is_theorem && !is_opaque)
        throw exception("invalid theorem declaration, theorems cannot be transparent");
    environment env = p.env();
    name real_n; // real name for this declaration
    if (is_private) {
        auto env_n = add_private_name(env, n, optional<unsigned>(hash(p.pos().first, p.pos().second)));
        env    = env_n.first;
        real_n = env_n.second;
    } else {
        name const & ns = get_namespace(env);
        real_n     = ns + n;
    }
    buffer<name> ls_buffer;
    expr type, value;
    level_param_names ls;
    {
        parser::local_scope scope1(p);
        parse_univ_params(p, ls_buffer);
        if (p.curr_is_token(g_assign)) {
            auto pos = p.pos();
            p.next();
            type  = p.save_pos(mk_expr_placeholder(), pos);
            value = p.parse_expr();
        } else if (p.curr_is_token(g_colon)) {
            p.next();
            {
                parser::param_universe_scope scope2(p);
                type = p.parse_expr();
            }
            p.check_token_next(g_assign, "invalid declaration, ':=' expected");
            value = p.parse_expr();
        } else {
            buffer<parameter> ps;
            optional<local_environment> lenv;
            {
                parser::param_universe_scope scope2(p);
                lenv = p.parse_binders(ps);
                p.check_token_next(g_colon, "invalid declaration, ':' expected");
                type = p.parse_scoped_expr(ps, *lenv);
            }
            p.check_token_next(g_assign, "invalid declaration, ':=' expected");
            value = p.parse_scoped_expr(ps, *lenv);
            type = p.pi_abstract(ps, type);
            value = p.lambda_abstract(ps, value);
        }
        update_univ_parameters(ls_buffer, collect_univ_params(value, collect_univ_params(type)), p);
        ls = to_list(ls_buffer.begin(), ls_buffer.end());
    }
    if (in_section(env)) {
        buffer<parameter> section_ps;
        collect_section_locals(type, value, p, section_ps);
        type = p.pi_abstract(section_ps, type);
        value = p.lambda_abstract(section_ps, value);
        levels section_ls = collect_section_levels(ls, p);
        buffer<expr> section_args;
        for (auto const & p : section_ps)
            section_args.push_back(p.m_local);
        expr ref = mk_app(mk_explicit(mk_constant(real_n, section_ls)), section_args);
        p.add_local_expr(n, ref);
    } else {
        if (real_n != n)
            env = add_alias(env, n, mk_constant(real_n));
    }
    if (is_theorem) {
        // TODO(Leo): delay theorems
        auto type_value = p.elaborate(n, type, value);
        type  = type_value.first;
        value = type_value.second;
        env = module::add(env, check(env, mk_theorem(real_n, ls, type, value)));
    } else {
        auto type_value = p.elaborate(n, type, value);
        type  = type_value.first;
        value = type_value.second;
        env = module::add(env, check(env, mk_definition(env, real_n, ls, type, value, is_opaque)));
    }
    return env;
}
environment definition_cmd(parser & p) {
    return definition_cmd_core(p, false, true);
}
environment abbreviation_cmd(parser & p) {
    return definition_cmd_core(p, false, false);
}
environment theorem_cmd(parser & p) {
    return definition_cmd_core(p, true, true);
}

static environment variables_cmd(parser & p) {
    auto pos = p.pos();
    buffer<name> ids;
    binder_info bi = parse_open_binder_info(p);
    while (!p.curr_is_token(g_colon)) {
        name id = p.check_id_next("invalid parameters declaration, identifier expected");
        check_atomic(id);
        ids.push_back(id);
    }
    p.next();
    optional<parser::local_scope> scope1;
    if (!in_section(p.env()))
        scope1.emplace(p);
    parser::param_universe_scope scope2(p);
    expr type = p.parse_expr();
    parse_close_binder_info(p, bi);
    level_param_names ls = to_level_param_names(collect_univ_params(type));
    type = p.elaborate(type);
    environment env = p.env();
    for (auto id : ids)
        env = declare_var(p, env, id, ls, type, true, bi, pos);
    return env;
}


void register_decl_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("universe",     "declare a global universe level", universe_cmd));
    add_cmd(r, cmd_info("variable",     "declare a new parameter", variable_cmd));
    add_cmd(r, cmd_info("axiom",        "declare a new axiom", axiom_cmd));
    add_cmd(r, cmd_info("definition",   "add new definition", definition_cmd));
    add_cmd(r, cmd_info("abbreviation", "add new abbreviation (aka transparent definition)", abbreviation_cmd));
    add_cmd(r, cmd_info("theorem",      "add new theorem", theorem_cmd));
    add_cmd(r, cmd_info("variables",    "declare new parameters", variables_cmd));
}
}
