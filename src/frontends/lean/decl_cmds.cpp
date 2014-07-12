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
#include "library/coercion.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/class.h"

namespace lean {
static name g_llevel_curly(".{");
static name g_rcurly("}");
static name g_colon(":");
static name g_assign(":=");
static name g_private("[private]");
static name g_inline("[inline]");
static name g_instance("[instance]");
static name g_coercion("[coercion]");

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
                               bool is_axiom, optional<binder_info> const & _bi, pos_info const & pos) {
    binder_info bi;
    if (_bi) bi = *_bi;
    if (in_section(p.env())) {
        p.add_local(p.save_pos(mk_local(n, type, bi), pos));
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

/** \brief If we are in a section, then add the new local levels to it. */
static void update_section_local_levels(parser & p, level_param_names const & new_ls) {
    if (in_section(p.env())) {
        for (auto const & l : new_ls)
            p.add_local_level(l, mk_param_univ(l));
    }
}

optional<binder_info> parse_binder_info(parser & p) {
    optional<binder_info> bi = p.parse_optional_binder_info();
    if (bi)
        check_in_section(p);
    return bi;
}

environment variable_cmd_core(parser & p, bool is_axiom) {
    auto pos = p.pos();
    optional<binder_info> bi = parse_binder_info(p);
    name n = p.check_id_next("invalid declaration, identifier expected");
    check_atomic(n);
    buffer<name> ls_buffer;
    if (p.curr_is_token(g_llevel_curly) && in_section(p.env()))
        throw parser_error("invalid declaration, axioms/parameters occurring in sections cannot be universe polymorphic", p.pos());
    optional<parser::local_scope> scope1;
    if (!in_section(p.env()))
        scope1.emplace(p);
    parse_univ_params(p, ls_buffer);
    expr type;
    if (!p.curr_is_token(g_colon)) {
        buffer<expr> ps;
        auto lenv = p.parse_binders(ps);
        p.check_token_next(g_colon, "invalid declaration, ':' expected");
        type = p.parse_scoped_expr(ps, lenv);
        type = p.pi_abstract(ps, type);
    } else {
        p.next();
        type = p.parse_expr();
    }
    p.parse_close_binder_info(bi);
    level_param_names ls;
    if (in_section(p.env())) {
        ls = to_level_param_names(collect_univ_params(type));
    } else {
        update_univ_parameters(ls_buffer, collect_univ_params(type), p);
        ls = to_list(ls_buffer.begin(), ls_buffer.end());
    }
    level_param_names new_ls;
    std::tie(type, new_ls) = p.elaborate_type(type);
    update_section_local_levels(p, new_ls);
    return declare_var(p, p.env(), n, append(ls, new_ls), type, is_axiom, bi, pos);
}
environment variable_cmd(parser & p) {
    return variable_cmd_core(p, false);
}
environment axiom_cmd(parser & p)    {
    return variable_cmd_core(p, true);
}

// Sort local_names by order of occurrence in the section, and copy the associated parameters to section_ps
void mk_section_params(name_set const & local_names, parser const & p, buffer<expr> & section_ps) {
    local_names.for_each([&](name const & n) {
            section_ps.push_back(*p.get_local(n));
        });
    std::sort(section_ps.begin(), section_ps.end(), [&](expr const & p1, expr const & p2) {
            return p.get_local_index(mlocal_name(p1)) < p.get_local_index(mlocal_name(p2));
        });
}

// Collect local (section) constants occurring in type and value, sort them, and store in section_ps
void collect_section_locals(expr const & type, expr const & value, parser const & p, buffer<expr> & section_ps) {
    name_set ls = collect_locals(type, collect_locals(value));
    return mk_section_params(ls, p, section_ps);
}

struct decl_modifiers {
    bool m_is_private;
    bool m_is_opaque;
    bool m_is_instance;
    bool m_is_coercion;
    decl_modifiers() {
        m_is_private  = false;
        m_is_opaque   = true;
        m_is_instance = false;
        m_is_coercion = false;
    }

    void parse(parser & p) {
        while (true) {
            if (p.curr_is_token(g_private)) {
                m_is_private = true;
                p.next();
            } else if (p.curr_is_token(g_inline)) {
                m_is_opaque = false;
                p.next();
            } else if (p.curr_is_token(g_instance)) {
                m_is_instance = true;
                p.next();
            } else if (p.curr_is_token(g_coercion)) {
                m_is_coercion = true;
                p.next();
            } else {
                break;
            }
        }
    }
};

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

environment definition_cmd_core(parser & p, bool is_theorem, bool _is_opaque) {
    name n = p.check_id_next("invalid declaration, identifier expected");
    check_atomic(n);
    environment env = p.env();
    decl_modifiers modifiers;
    name real_n; // real name for this declaration
    modifiers.m_is_opaque = _is_opaque;
    buffer<name> ls_buffer;
    expr type, value;
    level_param_names ls;
    {
        // Parse universe parameters
        parser::local_scope scope1(p);
        parse_univ_params(p, ls_buffer);

        // Parse modifiers
        modifiers.parse(p);
        if (is_theorem && !modifiers.m_is_opaque)
            throw exception("invalid theorem declaration, theorems cannot be transparent");
        if (modifiers.m_is_private) {
            auto env_n = add_private_name(env, n, optional<unsigned>(hash(p.pos().first, p.pos().second)));
            env    = env_n.first;
            real_n = env_n.second;
        } else {
            name const & ns = get_namespace(env);
            real_n     = ns + n;
        }

        if (p.curr_is_token(g_assign)) {
            auto pos = p.pos();
            p.next();
            type  = p.save_pos(mk_expr_placeholder(), pos);
            value = p.parse_expr();
        } else if (p.curr_is_token(g_colon)) {
            p.next();
            auto pos = p.pos();
            type = p.parse_expr();
            if (is_theorem && !p.curr_is_token(g_assign)) {
                value = mk_expr_placeholder();
            } else {
                p.check_token_next(g_assign, "invalid declaration, ':=' expected");
                value = p.save_pos(p.parse_expr(), pos);
            }
        } else {
            buffer<expr> ps;
            optional<local_environment> lenv;
            lenv = p.parse_binders(ps);
            if (p.curr_is_token(g_colon)) {
                p.next();
                auto pos = p.pos();
                type = p.parse_scoped_expr(ps, *lenv);
                if (is_theorem && !p.curr_is_token(g_assign)) {
                    value = p.save_pos(mk_expr_placeholder(), pos);
                } else {
                    p.check_token_next(g_assign, "invalid declaration, ':=' expected");
                    value = p.parse_scoped_expr(ps, *lenv);
                }
            } else {
                type = p.save_pos(mk_expr_placeholder(), p.pos());
                p.check_token_next(g_assign, "invalid declaration, ':=' expected");
                value = p.parse_scoped_expr(ps, *lenv);
            }
            type = p.pi_abstract(ps, type);
            value = p.lambda_abstract(ps, value);
        }
        update_univ_parameters(ls_buffer, collect_univ_params(value, collect_univ_params(type)), p);
        ls = to_list(ls_buffer.begin(), ls_buffer.end());
    }
    if (in_section(env)) {
        buffer<expr> section_ps;
        collect_section_locals(type, value, p, section_ps);
        type = p.pi_abstract(section_ps, type);
        value = p.lambda_abstract(section_ps, value);
        levels section_ls = collect_section_levels(ls, p);
        expr ref = mk_app(mk_explicit(mk_constant(real_n, section_ls)), section_ps);
        p.add_local_expr(n, ref);
    }
    if (real_n != n)
        env = add_decl_alias(env, n, mk_constant(real_n));
    level_param_names new_ls;
    if (is_theorem) {
        if (p.num_threads() > 1) {
            // add as axiom, and create a task to prove the theorem
            expr saved_type       = type;
            expr saved_value      = value;
            environment saved_env = env;
            std::tie(type, new_ls) = p.elaborate_type(type);
            env = module::add(env, check(env, mk_axiom(real_n, append(ls, new_ls), type)));
            p.add_delayed_theorem([=, &p]() {
                    level_param_names new_ls;
                    expr type, value;
                    std::tie(type, value, new_ls) = p.elaborate_definition_at(saved_env, n, saved_type, saved_value);
                    return check(saved_env, mk_theorem(real_n, append(ls, new_ls), type, value));
                });
        } else {
            std::tie(type, value, new_ls) = p.elaborate_definition(n, type, value);
            env = module::add(env, check(env, mk_theorem(real_n, append(ls, new_ls), type, value)));
        }
    } else {
        std::tie(type, value, new_ls) = p.elaborate_definition(n, type, value);
        env = module::add(env, check(env, mk_definition(env, real_n, append(ls, new_ls), type, value, modifiers.m_is_opaque)));
    }
    if (modifiers.m_is_instance)
        env = add_instance(env, real_n);
    if (modifiers.m_is_coercion)
        env = add_coercion(env, real_n, p.ios());
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
    optional<binder_info> bi = parse_binder_info(p);
    while (!p.curr_is_token(g_colon)) {
        name id = p.check_id_next("invalid parameters declaration, identifier expected");
        check_atomic(id);
        ids.push_back(id);
    }
    p.next();
    optional<parser::local_scope> scope1;
    if (!in_section(p.env()))
        scope1.emplace(p);
    expr type = p.parse_expr();
    p.parse_close_binder_info(bi);
    level_param_names ls = to_level_param_names(collect_univ_params(type));
    level_param_names new_ls;
    std::tie(type, new_ls) = p.elaborate_type(type);
    update_section_local_levels(p, new_ls);
    ls = append(ls, new_ls);
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
