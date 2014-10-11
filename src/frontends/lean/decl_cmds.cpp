/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/sstream.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "library/scoped_ext.h"
#include "library/aliases.h"
#include "library/private.h"
#include "library/protected.h"
#include "library/placeholder.h"
#include "library/locals.h"
#include "library/explicit.h"
#include "library/reducible.h"
#include "library/coercion.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/class.h"
#include "frontends/lean/tokens.h"

namespace lean {
static environment declare_universe(parser & p, environment env, name const & n) {
    if (in_section_or_context(env)) {
        p.add_local_level(n, mk_param_univ(n));
    } else {
        name const & ns = get_namespace(env);
        name full_n  = ns + n;
        env = module::add_universe(env, full_n);
        if (!ns.is_anonymous())
            env = add_level_alias(env, n, full_n);
    }
    return env;
}

environment universe_cmd(parser & p) {
    name n = p.check_id_next("invalid 'universe' command, identifier expected");
    return declare_universe(p, p.env(), n);
}

environment universes_cmd(parser & p) {
    if (!p.curr_is_identifier())
        throw parser_error("invalid 'universes' command, identifier expected", p.pos());
    environment env = p.env();
    while (p.curr_is_identifier()) {
        name n = p.get_name_val();
        p.next();
        env = declare_universe(p, env, n);
    }
    return env;
}

bool parse_univ_params(parser & p, buffer<name> & ps) {
    if (p.curr_is_token(get_llevel_curly_tk())) {
        p.next();
        while (!p.curr_is_token(get_rcurly_tk())) {
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

enum class variable_kind { Constant, Parameter, Variable, Axiom };

static void check_parameter_type(parser & p, name const & n, expr const & type, pos_info const & pos) {
    for_each(type, [&](expr const & e, unsigned) {
            if (is_local(e) && p.is_local_variable(e))
                throw parser_error(sstream() << "invalid parameter declaration '" << n << "', it depends on " <<
                                   "variable '" << local_pp_name(e) << "'", pos);
            return true;
        });
}

static environment declare_var(parser & p, environment env,
                               name const & n, level_param_names const & ls, expr const & type,
                               variable_kind k, optional<binder_info> const & _bi, pos_info const & pos) {
    binder_info bi;
    if (_bi) bi = *_bi;
    if (k == variable_kind::Parameter || k == variable_kind::Variable) {
        if (k == variable_kind::Parameter) {
            check_in_section_or_context(p);
            check_parameter_type(p, n, type, pos);
        }
        if (p.get_local(n))
            throw parser_error(sstream() << "invalid parameter/variable declaration, '"
                               << n << "' has already been declared", pos);
        name u = p.mk_fresh_name();
        expr l = p.save_pos(mk_local(u, n, type, bi), pos);
        p.add_local_expr(n, l, k == variable_kind::Variable);
        return env;
    } else {
        lean_assert(k == variable_kind::Constant || k == variable_kind::Axiom);
        name const & ns = get_namespace(env);
        name full_n  = ns + n;
        if (k == variable_kind::Axiom) {
            env = module::add(env, check(env, mk_axiom(full_n, ls, type)));
            p.add_decl_index(full_n, pos, get_axiom_tk(), type);
        } else {
            env = module::add(env, check(env, mk_constant_assumption(full_n, ls, type)));
            p.add_decl_index(full_n, pos, get_variable_tk(), type);
        }
        if (!ns.is_anonymous())
            env = add_expr_alias(env, n, full_n);
        return env;
    }
}

/** \brief If we are in a section, then add the new local levels to it. */
static void update_local_levels(parser & p, level_param_names const & new_ls, bool is_variable) {
    for (auto const & l : new_ls)
        p.add_local_level(l, mk_param_univ(l), is_variable);
}

optional<binder_info> parse_binder_info(parser & p, variable_kind k) {
    optional<binder_info> bi = p.parse_optional_binder_info();
    if (bi && k != variable_kind::Parameter && k != variable_kind::Variable)
        parser_error("invalid binder annotation, it can only be used to declare variables/parameters", p.pos());
    return bi;
}

static void check_variable_kind(parser & p, variable_kind k) {
    if (in_section_or_context(p.env())) {
        if (k == variable_kind::Axiom || k == variable_kind::Constant)
            throw parser_error("invalid declaration, 'constant/axiom' cannot be used in sections/contexts",
                               p.pos());
    } else {
        if (k == variable_kind::Parameter)
            throw parser_error("invalid declaration, 'parameter/hypothesis/conjecture' "
                               "can only be used in sections/contexts", p.pos());
    }
}

environment variable_cmd_core(parser & p, variable_kind k) {
    check_variable_kind(p, k);
    auto pos = p.pos();
    optional<binder_info> bi = parse_binder_info(p, k);
    name n = p.check_id_next("invalid declaration, identifier expected");
    buffer<name> ls_buffer;
    if (p.curr_is_token(get_llevel_curly_tk()) && (k == variable_kind::Parameter || k == variable_kind::Variable))
        throw parser_error("invalid declaration, only constants/axioms can be universe polymorphic", p.pos());
    optional<parser::local_scope> scope1;
    if (k == variable_kind::Constant || k == variable_kind::Axiom)
        scope1.emplace(p);
    parse_univ_params(p, ls_buffer);
    expr type;
    if (!p.curr_is_token(get_colon_tk())) {
        buffer<expr> ps;
        auto lenv = p.parse_binders(ps);
        p.check_token_next(get_colon_tk(), "invalid declaration, ':' expected");
        type = p.parse_scoped_expr(ps, lenv);
        type = Pi(ps, type, p);
    } else {
        p.next();
        type = p.parse_expr();
    }
    p.parse_close_binder_info(bi);
    level_param_names ls;
    if (ls_buffer.empty()) {
        ls = to_level_param_names(collect_univ_params(type));
    } else {
        update_univ_parameters(ls_buffer, collect_univ_params(type), p);
        ls = to_list(ls_buffer.begin(), ls_buffer.end());
    }
    level_param_names new_ls;
    list<expr> ctx = p.locals_to_context();
    std::tie(type, new_ls) = p.elaborate_type(type, ctx);
    if (k == variable_kind::Variable || k == variable_kind::Parameter)
        update_local_levels(p, new_ls, k == variable_kind::Variable);
    return declare_var(p, p.env(), n, append(ls, new_ls), type, k, bi, pos);
}
environment variable_cmd(parser & p) {
    return variable_cmd_core(p, variable_kind::Variable);
}
environment axiom_cmd(parser & p)    {
    return variable_cmd_core(p, variable_kind::Axiom);
}
environment constant_cmd(parser & p)    {
    return variable_cmd_core(p, variable_kind::Constant);
}
environment parameter_cmd(parser & p)    {
    return variable_cmd_core(p, variable_kind::Parameter);
}

static environment variables_cmd_core(parser & p, variable_kind k) {
    check_variable_kind(p, k);
    auto pos = p.pos();
    environment env = p.env();
    while (true) {
        optional<binder_info> bi = parse_binder_info(p, k);
        buffer<name> ids;
        while (!p.curr_is_token(get_colon_tk())) {
            name id = p.check_id_next("invalid parameters declaration, identifier expected");
            ids.push_back(id);
        }
        p.next();
        optional<parser::local_scope> scope1;
        if (k == variable_kind::Constant || k == variable_kind::Axiom)
            scope1.emplace(p);
        expr type = p.parse_expr();
        p.parse_close_binder_info(bi);
        level_param_names ls = to_level_param_names(collect_univ_params(type));
        list<expr> ctx = p.locals_to_context();
        for (auto id : ids) {
            // Hack: to make sure we get different universe parameters for each parameter.
            // Alternative: elaborate once and copy types replacing universes in new_ls.
            level_param_names new_ls;
            expr new_type;
            std::tie(new_type, new_ls) = p.elaborate_type(type, ctx);
            if (k == variable_kind::Variable || k == variable_kind::Parameter)
                update_local_levels(p, new_ls, k == variable_kind::Variable);
            new_ls = append(ls, new_ls);
            env = declare_var(p, env, id, new_ls, new_type, k, bi, pos);
        }
        if (!p.curr_is_token(get_lparen_tk()) && !p.curr_is_token(get_lcurly_tk()) &&
            !p.curr_is_token(get_ldcurly_tk()) && !p.curr_is_token(get_lbracket_tk()))
            break;
    }
    return env;
}
static environment variables_cmd(parser & p) {
    return variables_cmd_core(p, variable_kind::Variable);
}
static environment parameters_cmd(parser & p) {
    return variables_cmd_core(p, variable_kind::Parameter);
}
static environment constants_cmd(parser & p) {
    return variables_cmd_core(p, variable_kind::Constant);
}

struct decl_modifiers {
    bool               m_is_instance;
    bool               m_is_coercion;
    bool               m_is_reducible;
    optional<unsigned> m_priority;
    decl_modifiers():m_priority() {
        m_is_instance  = false;
        m_is_coercion  = false;
        m_is_reducible = false;
    }

    void parse(parser & p) {
        while (true) {
            auto pos = p.pos();
            if (p.curr_is_token(get_instance_tk())) {
                m_is_instance = true;
                p.next();
            } else if (p.curr_is_token(get_coercion_tk())) {
                m_is_coercion = true;
                p.next();
            } else if (p.curr_is_token(get_reducible_tk())) {
                m_is_reducible = true;
                p.next();
            } else if (auto it = parse_instance_priority(p)) {
                m_priority = *it;
                if (!m_is_instance)
                    throw parser_error("invalid '[priority]' occurrence, declaration must be marked as an '[instance]'", pos);
            } else {
                break;
            }
        }
    }
};

static void check_end_of_theorem(parser const & p) {
    if (!p.curr_is_command_like())
        throw parser_error("':=', '.', command, script, or end-of-file expected", p.pos());
}

static void erase_local_binder_info(buffer<expr> & ps) {
    for (expr & p : ps)
        p = update_local(p, binder_info());
}

environment definition_cmd_core(parser & p, bool is_theorem, bool is_opaque, bool is_private, bool is_protected) {
    lean_assert(!(is_theorem && !is_opaque));
    lean_assert(!(is_private && is_protected));
    auto n_pos = p.pos();
    unsigned start_line = n_pos.first;
    name n     = p.check_id_next("invalid declaration, identifier expected");
    decl_modifiers modifiers;
    name real_n; // real name for this declaration
    buffer<name> ls_buffer;
    expr type, value;
    level_param_names ls;
    {
        // Parse universe parameters
        parser::local_scope scope1(p);
        parse_univ_params(p, ls_buffer);

        // Parse modifiers
        modifiers.parse(p);

        if (p.curr_is_token(get_assign_tk())) {
            auto pos = p.pos();
            p.next();
            type  = p.save_pos(mk_expr_placeholder(), pos);
            value = p.parse_expr();
        } else if (p.curr_is_token(get_colon_tk())) {
            p.next();
            auto pos = p.pos();
            type = p.parse_expr();
            if (is_theorem && !p.curr_is_token(get_assign_tk())) {
                check_end_of_theorem(p);
                value = mk_expr_placeholder();
            } else {
                p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
                value = p.save_pos(p.parse_expr(), pos);
            }
        } else {
            buffer<expr> ps;
            optional<local_environment> lenv;
            bool last_block_delimited = false;
            lenv = p.parse_binders(ps, last_block_delimited);
            auto pos = p.pos();
            if (p.curr_is_token(get_colon_tk())) {
                p.next();
                type = p.parse_scoped_expr(ps, *lenv);
                if (is_theorem && !p.curr_is_token(get_assign_tk())) {
                    check_end_of_theorem(p);
                    value = p.save_pos(mk_expr_placeholder(), pos);
                } else {
                    p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
                    value = p.parse_scoped_expr(ps, *lenv);
                }
            } else {
                if (!last_block_delimited && !ps.empty() &&
                    !is_placeholder(mlocal_type(ps.back()))) {
                    throw parser_error("invalid declaration, ambiguous parameter declaration, "
                                       "(solution: put parentheses around parameters)",
                                       pos);
                }
                type = p.save_pos(mk_expr_placeholder(), p.pos());
                p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
                value = p.parse_scoped_expr(ps, *lenv);
            }
            type  = Pi(ps, type, p);
            erase_local_binder_info(ps);
            value = Fun(ps, value, p);
        }
    }
    unsigned end_line = p.pos().first;

    if (p.used_sorry())
        p.declare_sorry();
    environment env = p.env();

    if (is_private) {
        auto env_n = add_private_name(env, n, optional<unsigned>(hash(p.pos().first, p.pos().second)));
        env    = env_n.first;
        real_n = env_n.second;
    } else {
        name const & ns = get_namespace(env);
        real_n     = ns + n;
    }

    if (p.has_locals()) {
        buffer<expr> section_ps;
        collect_section_locals(type, value, p, section_ps);
        type = Pi_as_is(section_ps, type, p);
        buffer<expr> section_value_ps;
        section_value_ps.append(section_ps);
        erase_local_binder_info(section_value_ps);
        value = Fun_as_is(section_value_ps, value, p);
        update_univ_parameters(ls_buffer, collect_univ_params(value, collect_univ_params(type)), p);
        ls = to_list(ls_buffer.begin(), ls_buffer.end());
        levels section_ls = collect_section_nonvar_levels(p, ls);
        remove_section_variables(p, section_ps);
        if (!section_ps.empty()) {
            expr ref = mk_section_local_ref(real_n, section_ls, section_ps);
            p.add_local_expr(n, ref);
        } else if (section_ls) {
            expr ref = mk_constant(real_n, section_ls);
            p.add_local_expr(n, ref);
        }
    } else {
        update_univ_parameters(ls_buffer, collect_univ_params(value, collect_univ_params(type)), p);
        ls = to_list(ls_buffer.begin(), ls_buffer.end());
    }
    expr pre_type  = type;
    expr pre_value = value;
    level_param_names new_ls;
    bool found_cached = false;
    if (p.are_info_lines_valid(start_line, end_line)) {
        // we only use the cache if the information associated with the line is valid
        if (auto it = p.find_cached_definition(real_n, pre_type, pre_value)) {
            optional<certified_declaration> cd;
            try {
                level_param_names c_ls; expr c_type, c_value;
                std::tie(c_ls, c_type, c_value) = *it;
                if (is_theorem)
                    cd = check(env, mk_theorem(real_n, c_ls, c_type, c_value));
                else
                    cd = check(env, mk_definition(env, real_n, c_ls, c_type, c_value, is_opaque));
                if (!is_private)
                    p.add_decl_index(real_n, n_pos, p.get_cmd_token(), c_type);
                env = module::add(env, *cd);
                found_cached = true;
            } catch (exception&) {}
        }
    }

    if (!found_cached) {
        if (is_theorem) {
            auto type_pos = p.pos_of(type);
            bool clear_pre_info = false; // we don't want to clear pre_info data until we process the proof.
            std::tie(type, new_ls) = p.elaborate_type(type, list<expr>(), clear_pre_info);
            check_no_metavar(env, real_n, type, true);
            ls = append(ls, new_ls);
            expr type_as_is = p.save_pos(mk_as_is(type), type_pos);
            if (!p.collecting_info() && p.num_threads() > 1) {
                // add as axiom, and create a task to prove the theorem
                p.add_delayed_theorem(env, real_n, ls, type_as_is, value);
                env = module::add(env, check(env, mk_axiom(real_n, ls, type)));
            } else {
                std::tie(type, value, new_ls) = p.elaborate_definition(n, type_as_is, value, is_opaque);
                new_ls = append(ls, new_ls);
                env = module::add(env, check(env, mk_theorem(real_n, new_ls, type, value)));
                p.cache_definition(real_n, pre_type, pre_value, new_ls, type, value);
            }
        } else {
            std::tie(type, value, new_ls) = p.elaborate_definition(n, type, value, is_opaque);
            new_ls = append(ls, new_ls);
            env = module::add(env, check(env, mk_definition(env, real_n, new_ls, type, value, is_opaque)));
            p.cache_definition(real_n, pre_type, pre_value, new_ls, type, value);
        }
        if (!is_private)
            p.add_decl_index(real_n, n_pos, p.get_cmd_token(), type);
    }

    if (real_n != n)
        env = add_expr_alias_rec(env, n, real_n);
    if (modifiers.m_is_instance) {
        bool persistent = true;
        if (modifiers.m_priority) {
            #if defined(__GNUC__) && !defined(__CLANG__)
            #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
            #endif
            env = add_instance(env, real_n, *modifiers.m_priority, persistent);
        } else {
            env = add_instance(env, real_n, persistent);
        }
    }
    if (modifiers.m_is_coercion)
        env = add_coercion(env, real_n, p.ios());
    if (is_protected)
        env = add_protected(env, real_n);
    if (modifiers.m_is_reducible)
        env = set_reducible(env, real_n, reducible_status::On);
    return env;
}
environment definition_cmd(parser & p) {
    return definition_cmd_core(p, false, false, false, false);
}
environment opaque_definition_cmd(parser & p) {
    p.check_token_next(get_definition_tk(), "invalid 'opaque' definition, 'definition' expected");
    return definition_cmd_core(p, false, true, false, false);
}
environment theorem_cmd(parser & p) {
    return definition_cmd_core(p, true, true, false, false);
}
environment private_definition_cmd(parser & p) {
    bool is_theorem = false;
    bool is_opaque  = false;
    if (p.curr_is_token_or_id(get_opaque_tk())) {
        is_opaque = true;
        p.next();
        p.check_token_next(get_definition_tk(), "invalid 'private' definition, 'definition' expected");
    } else if (p.curr_is_token_or_id(get_definition_tk())) {
        p.next();
    } else if (p.curr_is_token_or_id(get_theorem_tk())) {
        p.next();
        is_theorem = true;
        is_opaque  = true;
    } else {
        throw parser_error("invalid 'private' definition/theorem, 'definition' or 'theorem' expected", p.pos());
    }
    return definition_cmd_core(p, is_theorem, is_opaque, true, false);
}
environment protected_definition_cmd(parser & p) {
    bool is_theorem = false;
    bool is_opaque  = false;
    if (p.curr_is_token_or_id(get_opaque_tk())) {
        is_opaque = true;
        p.next();
        p.check_token_next(get_definition_tk(), "invalid 'protected' definition, 'definition' expected");
    } else if (p.curr_is_token_or_id(get_definition_tk())) {
        p.next();
    } else if (p.curr_is_token_or_id(get_theorem_tk())) {
        p.next();
        is_theorem = true;
        is_opaque  = true;
    } else {
        throw parser_error("invalid 'protected' definition/theorem, 'definition' or 'theorem' expected", p.pos());
    }
    return definition_cmd_core(p, is_theorem, is_opaque, false, true);
}

environment include_cmd_core(parser & p, bool include) {
    if (!p.curr_is_identifier())
        throw parser_error(sstream() << "invalid include/omit command, identifier expected", p.pos());
    while (p.curr_is_identifier()) {
        auto pos = p.pos();
        name n = p.get_name_val();
        p.next();
        if (!p.get_local(n))
            throw parser_error(sstream() << "invalid include/omit command, '" << n << "' is not a parameter/variable", pos);
        if (include) {
            if (p.is_include_variable(n))
                throw parser_error(sstream() << "invalid include command, '" << n << "' has already been included", pos);
            p.include_variable(n);
        } else {
            if (!p.is_include_variable(n))
                throw parser_error(sstream() << "invalid omit command, '" << n << "' has not been included", pos);
            p.omit_variable(n);
        }
    }
    return p.env();
}

environment include_cmd(parser & p) {
    return include_cmd_core(p, true);
}

environment omit_cmd(parser & p) {
    return include_cmd_core(p, false);
}

void register_decl_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("universe",     "declare a universe level", universe_cmd));
    add_cmd(r, cmd_info("universes",    "declare universe levels", universes_cmd));
    add_cmd(r, cmd_info("variable",     "declare a new variable", variable_cmd));
    add_cmd(r, cmd_info("parameter",    "declare a new parameter", parameter_cmd));
    add_cmd(r, cmd_info("constant",     "declare a new constant (aka top-level variable)", constant_cmd));
    add_cmd(r, cmd_info("axiom",        "declare a new axiom", axiom_cmd));
    add_cmd(r, cmd_info("variables",    "declare new variables", variables_cmd));
    add_cmd(r, cmd_info("parameters",   "declare new parameters", parameters_cmd));
    add_cmd(r, cmd_info("constants",    "declare new constants (aka top-level variables)", constants_cmd));
    add_cmd(r, cmd_info("definition",   "add new definition", definition_cmd));
    add_cmd(r, cmd_info("opaque",       "add new opaque definition", opaque_definition_cmd));
    add_cmd(r, cmd_info("private",      "add new private definition/theorem", private_definition_cmd));
    add_cmd(r, cmd_info("protected",    "add new protected definition/theorem", protected_definition_cmd));
    add_cmd(r, cmd_info("theorem",      "add new theorem", theorem_cmd));
    add_cmd(r, cmd_info("include",      "force section parameter/variable to be included", include_cmd));
    add_cmd(r, cmd_info("omit",         "undo 'include' command", omit_cmd));
}
}
