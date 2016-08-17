/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <algorithm>
#include "util/fresh_name.h"
#include "util/sstream.h"
#include "util/timeit.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "library/scoped_ext.h"
#include "library/aliases.h"
#include "library/private.h"
#include "library/protected.h"
#include "library/noncomputable.h"
#include "library/placeholder.h"
#include "library/locals.h"
#include "library/explicit.h"
#include "library/abbreviation.h"
#include "library/flycheck.h"
#include "library/error_handling.h"
#include "library/equations_compiler/equations.h"
#include "library/compiler/rec_fn_macro.h"
#include "library/compiler/vm_compiler.h"
#include "library/vm/vm.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/update_environment_exception.h"
#include "frontends/lean/nested_declaration.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/definition_cmds.h"
#include "frontends/lean/inductive_cmds.h"

// We don't display profiling information for declarations that take less than 0.01 secs
#ifndef LEAN_PROFILE_THRESHOLD
#define LEAN_PROFILE_THRESHOLD 0.01
#endif

namespace lean {
// TODO(Leo): delete
void update_univ_parameters(parser & p, buffer<name> & lp_names, name_set const & found);

static environment declare_universe(parser & p, environment env, name const & n, bool local) {
    if (local) {
        p.add_local_level(n, mk_param_univ(n), local);
    } else if (in_section(env)) {
        p.add_local_level(n, mk_param_univ(n), false);
    } else {
        name const & ns = get_namespace(env);
        name full_n  = ns + n;
        env = module::add_universe(env, full_n);
        if (!ns.is_anonymous())
            env = add_level_alias(env, n, full_n);
    }
    return env;
}

static environment universes_cmd_core(parser & p, bool local) {
    if (!p.curr_is_identifier())
        throw parser_error("invalid 'universes' command, identifier expected", p.pos());
    environment env = p.env();
    while (p.curr_is_identifier()) {
        name n = p.get_name_val();
        p.next();
        env = declare_universe(p, env, n, local);
    }
    return env;
}

static environment universe_cmd(parser & p) {
    if (p.curr_is_token(get_variables_tk())) {
        p.next();
        return universes_cmd_core(p, true);
    } else {
        bool local = false;
        if (p.curr_is_token(get_variable_tk())) {
            p.next();
            local = true;
        }
        name n = p.check_decl_id_next("invalid 'universe' command, identifier expected");
        return declare_universe(p, p.env(), n, local);
    }
}

static environment universes_cmd(parser & p) {
    return universes_cmd_core(p, false);
}

enum class variable_kind { Constant, Parameter, Variable, Axiom, MetaConstant };

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
                               variable_kind k, optional<binder_info> const & _bi, pos_info const & pos,
                               bool is_protected) {
    binder_info bi;
    if (_bi) bi = *_bi;
    if (k == variable_kind::Parameter || k == variable_kind::Variable) {
        if (k == variable_kind::Parameter) {
            check_in_section(p);
            check_parameter_type(p, n, type, pos);
        }
        if (p.get_local(n))
            throw parser_error(sstream() << "invalid parameter/variable declaration, '"
                               << n << "' has already been declared", pos);
        name u = mk_fresh_name();
        expr l = p.save_pos(mk_local(u, n, type, bi), pos);
        if (k == variable_kind::Parameter)
            p.add_parameter(n, l);
        else
            p.add_variable(n, l);
        return env;
    } else {
        lean_assert(k == variable_kind::Constant || k == variable_kind::Axiom || k == variable_kind::MetaConstant);
        name const & ns = get_namespace(env);
        name full_n  = ns + n;
        expr new_type = postprocess(env, type);
        if (k == variable_kind::Axiom) {
            env = module::add(env, check(env, mk_axiom(full_n, ls, new_type)));
            p.add_decl_index(full_n, pos, get_axiom_tk(), new_type);
        } else {
            bool is_trusted = k == variable_kind::Constant;
            env = module::add(env, check(env, mk_constant_assumption(full_n, ls, new_type, is_trusted)));
            p.add_decl_index(full_n, pos, get_variable_tk(), new_type);
        }
        if (!ns.is_anonymous()) {
            if (is_protected)
                env = add_expr_alias(env, get_protected_shortest_name(full_n), full_n);
            else
                env = add_expr_alias(env, n, full_n);
        }
        if (is_protected)
            env = add_protected(env, full_n);
        env = ensure_decl_namespaces(env, full_n);
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
    if (in_section(p.env())) {
        if (k == variable_kind::Axiom || k == variable_kind::Constant)
            throw parser_error("invalid declaration, 'constant/axiom' cannot be used in sections",
                               p.pos());
    } else if (!in_section(p.env()) && k == variable_kind::Parameter) {
        throw parser_error("invalid declaration, 'parameter/hypothesis/conjecture' "
                           "can only be used in sections", p.pos());
    }
}

static void update_local_binder_info(parser & p, variable_kind k, name const & n,
                                     optional<binder_info> const & bi, pos_info const & pos) {
    binder_info new_bi;
    if (bi) new_bi = *bi;
    if (k == variable_kind::Parameter) {
        if (p.is_local_variable(n))
            throw parser_error(sstream() << "invalid parameter binder type update, '"
                               << n << "' is a variable", pos);
        if (!p.update_local_binder_info(n, new_bi))
            throw parser_error(sstream() << "invalid parameter binder type update, '"
                               << n << "' is not a parameter", pos);
    } else {
        if (!p.update_local_binder_info(n, new_bi) || !p.is_local_variable(n))
            throw parser_error(sstream() << "invalid variable binder type update, '"
                               << n << "' is not a variable", pos);
    }
}

static bool curr_is_binder_annotation(parser & p) {
    return p.curr_is_token(get_lparen_tk()) || p.curr_is_token(get_lcurly_tk()) ||
           p.curr_is_token(get_ldcurly_tk()) || p.curr_is_token(get_lbracket_tk());
}

static environment variable_cmd_core(parser & p, variable_kind k, bool is_protected = false) {
    check_variable_kind(p, k);
    auto pos = p.pos();
    optional<binder_info> bi = parse_binder_info(p, k);
    optional<parser::local_scope> scope1;
    name n;
    expr type;
    buffer<name> ls_buffer;
    if (bi && bi->is_inst_implicit() && (k == variable_kind::Parameter || k == variable_kind::Variable)) {
        /* instance implicit */
        if (p.curr_is_identifier()) {
            auto n_pos = p.pos();
            n = p.get_name_val();
            p.next();
            if (p.curr_is_token(get_colon_tk())) {
                /* simple decl: variable [decA : decidable A] */
                p.next();
                type = p.parse_expr();
            } else if (p.curr_is_token(get_rbracket_tk())) {
                /* annotation update: variable [decA] */
                p.parse_close_binder_info(bi);
                update_local_binder_info(p, k, n, bi, pos);
                return p.env();
            } else {
                /* anonymous : variable [decidable A] */
                expr left    = p.id_to_expr(n, n_pos);
                n            = p.mk_anonymous_inst_name();
                unsigned rbp = 0;
                while (rbp < p.curr_lbp()) {
                    left = p.parse_led(left);
                }
                type = left;
            }
        } else {
            /* anonymous : variable [forall x y, decidable (x = y)] */
            n    = p.mk_anonymous_inst_name();
            type = p.parse_expr();
        }
    } else {
        /* non instance implicit cases */
        n = p.check_decl_id_next("invalid declaration, identifier expected");
        if (p.curr_is_token(get_llevel_curly_tk()) && (k == variable_kind::Parameter || k == variable_kind::Variable))
            throw parser_error("invalid declaration, only constants/axioms can be universe polymorphic", p.pos());
        if (k == variable_kind::Constant || k == variable_kind::Axiom)
            scope1.emplace(p);
        parse_univ_params(p, ls_buffer);
        if (!p.curr_is_token(get_colon_tk())) {
            if (!curr_is_binder_annotation(p) && (k == variable_kind::Parameter || k == variable_kind::Variable)) {
                p.parse_close_binder_info(bi);
                update_local_binder_info(p, k, n, bi, pos);
                return p.env();
            } else {
                buffer<expr> ps;
                unsigned rbp = 0;
                auto lenv = p.parse_binders(ps, rbp);
                p.check_token_next(get_colon_tk(), "invalid declaration, ':' expected");
                type = p.parse_scoped_expr(ps, lenv);
                type = Pi(ps, type, p);
            }
        } else {
            p.next();
            type = p.parse_expr();
        }
    }
    p.parse_close_binder_info(bi);
    check_command_period_or_eof(p);
    level_param_names ls;
    if (ls_buffer.empty()) {
        ls = to_level_param_names(collect_univ_params(type));
    } else {
        update_univ_parameters(p, ls_buffer, collect_univ_params(type));
        ls = to_list(ls_buffer.begin(), ls_buffer.end());
    }
    level_param_names new_ls;
    list<expr> ctx = p.locals_to_context();
    std::tie(type, new_ls) = p.elaborate_type(ctx, type);
    if (k == variable_kind::Variable || k == variable_kind::Parameter)
        update_local_levels(p, new_ls, k == variable_kind::Variable);
    return declare_var(p, p.env(), n, append(ls, new_ls), type, k, bi, pos, is_protected);
}
static environment variable_cmd(parser & p) {
    return variable_cmd_core(p, variable_kind::Variable);
}
static environment axiom_cmd(parser & p)    {
    return variable_cmd_core(p, variable_kind::Axiom);
}
static environment constant_cmd(parser & p)    {
    return variable_cmd_core(p, variable_kind::Constant);
}
static environment meta_constant_cmd(parser & p)    {
    return variable_cmd_core(p, variable_kind::MetaConstant);
}
static environment parameter_cmd(parser & p)    {
    return variable_cmd_core(p, variable_kind::Parameter);
}

static environment variables_cmd_core(parser & p, variable_kind k, bool is_protected = false) {
    check_variable_kind(p, k);
    auto pos = p.pos();
    environment env = p.env();

    optional<binder_info> bi = parse_binder_info(p, k);
    buffer<name> ids;
    optional<parser::local_scope> scope1;
    expr type;
    if (bi && bi->is_inst_implicit() && (k == variable_kind::Parameter || k == variable_kind::Variable)) {
        /* instance implicit */
        if (p.curr_is_identifier()) {
            auto id_pos = p.pos();
            name id = p.get_name_val();
            p.next();
            if (p.curr_is_token(get_colon_tk())) {
                /* simple decl: variables [decA : decidable A] */
                p.next();
                ids.push_back(id);
                type = p.parse_expr();
            } else if (p.curr_is_token(get_rbracket_tk())) {
                /* annotation update: variables [decA] */
                p.parse_close_binder_info(bi);
                update_local_binder_info(p, k, id, bi, pos);
                if (curr_is_binder_annotation(p))
                    return variables_cmd_core(p, k);
                else
                    return env;
            } else {
                /* anonymous : variables [decidable A] */
                expr left    = p.id_to_expr(id, id_pos);
                id           = p.mk_anonymous_inst_name();
                unsigned rbp = 0;
                while (rbp < p.curr_lbp()) {
                    left = p.parse_led(left);
                }
                ids.push_back(id);
                type = left;
            }
        } else {
            /* anonymous : variables [forall x y, decidable (x = y)] */
            name id = p.mk_anonymous_inst_name();
            ids.push_back(id);
            type = p.parse_expr();
        }
    } else {
        /* non instance implicit cases */
        while (p.curr_is_identifier()) {
            name id = p.get_name_val();
            p.next();
            ids.push_back(id);
        }
        if (p.curr_is_token(get_colon_tk())) {
            p.next();
        } else {
            /* binder annotation update */
            /* example: variables (A) */
            if (k == variable_kind::Parameter || k == variable_kind::Variable) {
                p.parse_close_binder_info(bi);
                for (name const & id : ids) {
                    update_local_binder_info(p, k, id, bi, pos);
                }
                if (curr_is_binder_annotation(p))
                    return variables_cmd_core(p, k);
                else
                    return env;
            } else {
                throw parser_error("invalid variables/constants/axioms declaration, ':' expected", pos);
            }
        }
        if (k == variable_kind::Constant || k == variable_kind::Axiom)
            scope1.emplace(p);
        type = p.parse_expr();
    }
    p.parse_close_binder_info(bi);

    level_param_names ls = to_level_param_names(collect_univ_params(type));
    list<expr> ctx = p.locals_to_context();
    for (auto id : ids) {
        // Hack: to make sure we get different universe parameters for each parameter.
        // Alternative: elaborate once and copy types replacing universes in new_ls.
        level_param_names new_ls;
        expr new_type;
        check_command_period_open_binder_or_eof(p);
        std::tie(new_type, new_ls) = p.old_elaborate_type(type, ctx);
        if (k == variable_kind::Variable || k == variable_kind::Parameter)
            update_local_levels(p, new_ls, k == variable_kind::Variable);
        new_ls = append(ls, new_ls);
        env = declare_var(p, env, id, new_ls, new_type, k, bi, pos, is_protected);
    }
    if (curr_is_binder_annotation(p)) {
        if (k == variable_kind::Constant || k == variable_kind::Axiom) {
            // Hack: temporarily update the parser environment.
            // We must do that to be able to process
            //    constants (A : Type) (a : A)
            parser::local_scope scope2(p, env);
            return variables_cmd_core(p, k);
        } else {
            return variables_cmd_core(p, k);
        }
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
static environment axioms_cmd(parser & p) {
    return variables_cmd_core(p, variable_kind::Axiom);
}

static void check_end_of_theorem(parser const & p) {
    if (!p.curr_is_command_like())
        throw parser_error("':=', '.', command, script, or end-of-file expected", p.pos());
}
static void erase_local_binder_info(buffer<expr> & ps) {
    for (expr & p : ps)
        p = update_local(p, binder_info());
}
static bool is_curr_with_or_comma_or_bar(parser & p) {
    return p.curr_is_token(get_with_tk()) || p.curr_is_token(get_comma_tk()) || p.curr_is_token(get_bar_tk());
}

[[ noreturn ]] static void throw_invalid_equation_lhs(name const & n, pos_info const & p) {
    throw parser_error(sstream() << "invalid recursive equation, head symbol '"
                       << n << "' in the left-hand-side does not correspond to function(s) being defined", p);
}

static void check_eqn_prefix(parser & p) {
    if (!is_eqn_prefix(p))
        throw parser_error("invalid declaration, ',' or '|' expected", p.pos());
    p.next();
}

static optional<expr> is_equation_fn(buffer<expr> const & fns, name const & fn_name) {
    for (expr const & fn : fns) {
        if (local_pp_name(fn) == fn_name)
            return some_expr(fn);
    }
    return none_expr();
}


static expr get_equation_fn(buffer<expr> const & fns, name const & fn_name, pos_info const & lhs_pos) {
    if (auto it = is_equation_fn(fns, fn_name))
        return *it;
    throw_invalid_equation_lhs(fn_name, lhs_pos);
}

static void parse_equations_core(parser & p, buffer<expr> const & fns, buffer<expr> & eqns, bool bar_only,
                                 bool is_meta) {
    if (!is_meta) {
        for (expr const & fn : fns)
            p.add_local(fn);
    }
    while (true) {
        expr lhs;
        {
            parser::undef_id_to_local_scope scope2(p);
            buffer<expr> lhs_args;
            auto lhs_pos = p.pos();
            if (p.curr_is_token(get_explicit_tk())) {
                p.next();
                name fn_name = p.check_decl_id_next("invalid recursive equation, identifier expected");
                lhs_args.push_back(p.save_pos(mk_explicit(get_equation_fn(fns, fn_name, lhs_pos)), lhs_pos));
            } else {
                expr first = p.parse_pattern_or_expr(get_max_prec());
                expr fn    = first;
                if (is_explicit(fn))
                    fn = get_explicit_arg(fn);
                if (is_local(fn) && is_equation_fn(fns, local_pp_name(fn))) {
                    lhs_args.push_back(p.patexpr_to_expr(first));
                } else if (fns.size() == 1) {
                    lhs_args.push_back(p.save_pos(mk_explicit(fns[0]), lhs_pos));
                    lhs_args.push_back(first);
                } else {
                    throw parser_error("invalid recursive equation, head symbol in left-hand-side is not a constant",
                                       lhs_pos);
                }
            }
            while (!p.curr_is_token(get_assign_tk()))
                lhs_args.push_back(p.parse_pattern_or_expr(get_max_prec()));
            lean_assert(lhs_args.size() > 0);
            lhs = lhs_args[0];
            for (unsigned i = 1; i < lhs_args.size(); i++)
                lhs = copy_tag(lhs_args[i], mk_app(lhs, lhs_args[i]));
        }
        buffer<expr> locals;
        bool skip_main_fn = true;
        lhs = p.patexpr_to_pattern(lhs, skip_main_fn, locals);
        auto assign_pos = p.pos();
        p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
        {
            parser::local_scope scope2(p);
            for (expr const & local : locals)
                p.add_local(local);
            expr rhs = p.parse_expr();
            eqns.push_back(Fun(fns, Fun(locals, p.save_pos(mk_equation(lhs, rhs), assign_pos), p)));
        }
        if (!is_eqn_prefix(p, bar_only))
            break;
        p.next();
    }
}

expr parse_equations(parser & p, name const & n, expr const & type, buffer<name> & auxs,
                     optional<local_environment> const & lenv, buffer<expr> const & ps,
                     pos_info const & def_pos, bool is_meta) {
    buffer<expr> fns;
    buffer<expr> eqns;
    {
        parser::local_scope scope1(p, lenv);
        for (expr const & param : ps)
            p.add_local(param);
        lean_assert(is_curr_with_or_comma_or_bar(p));
        fns.push_back(mk_local(n, type, mk_rec_info(true)));
        if (p.curr_is_token(get_with_tk())) {
            while (p.curr_is_token(get_with_tk())) {
                p.next();
                auto pos = p.pos();
                name g_name = p.check_decl_id_next("invalid declaration, identifier expected");
                p.check_token_next(get_colon_tk(), "invalid declaration, ':' expected");
                expr g_type = p.parse_expr();
                expr g      = p.save_pos(mk_local(g_name, g_type, mk_rec_info(true)), pos);
                auxs.push_back(g_name);
                fns.push_back(g);
            }
        }
        check_eqn_prefix(p);
        if (p.curr_is_token(get_none_tk())) {
            // no equations have been provided
            p.next();
            eqns.push_back(Fun(fns, mk_no_equation(), p));
        } else {
            bool bar_only = false;
            parse_equations_core(p, fns, eqns, bar_only, is_meta);
        }
    }
    if (p.curr_is_token(get_using_well_founded_tk())) {
        p.next();
        expr R   = p.parse_expr(get_max_prec());
        expr Hwf = p.parse_expr(get_max_prec());
        return p.save_pos(mk_equations(fns.size(), eqns.size(), eqns.data(), R, Hwf), def_pos);
    } else {
        return p.save_pos(mk_equations(fns.size(), eqns.size(), eqns.data()), def_pos);
    }
}

/** \brief Parse a sequence of equations of the form <tt>| lhs := rhs</tt> */
expr parse_local_equations(parser & p, expr const & fn) {
    lean_assert(p.curr_is_token(get_bar_tk()));
    auto pos = p.pos();
    p.next();
    buffer<expr> fns;
    buffer<expr> eqns;
    fns.push_back(fn);
    bool bar_only = true;
    bool is_meta  = false;
    parse_equations_core(p, fns, eqns, bar_only, is_meta);
    return p.save_pos(mk_equations(fns.size(), eqns.size(), eqns.data()), pos);
}

void collect_locals_ignoring_tactics(expr const & e, collected_locals & ls);

// Collect local constants occurring in type and value, sort them, and store in ctx_ps
void collect_locals(expr const & type, expr const & value, parser const & p, buffer<expr> & ctx_ps) {
    collected_locals ls;
    buffer<expr> include_vars;
    p.get_include_variables(include_vars);
    for (expr const & param : include_vars) {
        if (is_local(param)) {
            collect_locals_ignoring_tactics(mlocal_type(param), ls);
            ls.insert(param);
        }
    }
    collect_locals_ignoring_tactics(type, ls);
    collect_locals_ignoring_tactics(value, ls);
    collect_annonymous_inst_implicit(p, ls);
    sort_locals(ls.get_collected(), p, ctx_ps);
}

class definition_cmd_fn {
    parser &          m_p;
    environment       m_env;
    def_cmd_kind      m_kind;
    bool              m_is_private;
    bool              m_is_protected;
    bool              m_is_noncomputable;
    pos_info          m_pos;

    name              m_name;
    decl_attributes   m_attributes;
    name              m_real_name; // real name for this declaration
    buffer<name>      m_ls_buffer;
    buffer<name>      m_aux_decls; // user provided names for aux_decls
    buffer<name>      m_real_aux_names; // real names for aux_decls
    buffer<expr>      m_aux_types; // types of auxiliary decls
    expr              m_type;
    expr              m_value;
    level_param_names m_ls;
    pos_info          m_end_pos;

    expr              m_pre_type;
    expr              m_pre_value;

    // Checkpoint for processing definition/theorem as axiom in case of
    // failure
    optional<expr>        m_type_checkpoint;
    optional<environment> m_env_checkpoint;
    buffer<name>          m_ls_buffer_checkpoint;

    void save_checkpoint() {
        if (m_kind != Example) {
            m_type_checkpoint      = m_type;
            m_env_checkpoint       = m_env;
            m_ls_buffer_checkpoint = m_ls_buffer;
        }
    }

    bool is_meta() const { return m_kind == MetaDefinition; }
    bool is_trusted() const { return !is_meta(); }
    bool is_definition() const { return m_kind == Definition || m_kind == MetaDefinition || m_kind == Abbreviation || m_kind == LocalAbbreviation; }
    bool is_example() const { return m_kind == Example; }
    unsigned start_line() const { return m_pos.first; }
    unsigned end_line() const { return m_end_pos.first; }

    void parse_name() {
        if (m_kind == Example)
            m_name = get_this_tk();
        else
            m_name = m_p.check_decl_id_next("invalid declaration, identifier expected");
    }

    expr extract_nested(expr const & v) {
        expr new_v;
        std::tie(m_env, new_v) = extract_nested_declarations(m_env, m_p.ios(), m_name, v);
        return new_v;
    }

    void add_meta_rec_ref() {
        if (m_kind == MetaDefinition) {
            m_env = m_p.add_local_ref(m_env, m_name, mk_rec_fn_macro(m_real_name, mk_expr_placeholder()));
        }
    }

    void parse_type_value() {
        // Parse universe parameters
        parser::local_scope scope1(m_p);
        parse_univ_params(m_p, m_ls_buffer);

        if (m_p.curr_is_token(get_assign_tk())) {
            auto pos = m_p.pos();
            m_p.next();
            m_type  = m_p.save_pos(mk_expr_placeholder(), pos);
            add_meta_rec_ref();
            m_value = m_p.parse_expr();
        } else if (m_p.curr_is_token(get_colon_tk())) {
            m_p.next();
            auto pos = m_p.pos();
            m_type = m_p.parse_expr();
            save_checkpoint();
            add_meta_rec_ref();
            if (is_curr_with_or_comma_or_bar(m_p)) {
                allow_nested_decls_scope scope2(is_definition());
                m_value = parse_equations(m_p, m_name, m_type, m_aux_decls,
                                          optional<local_environment>(), buffer<expr>(), m_pos, is_meta());
            } else if (!is_definition() && !m_p.curr_is_token(get_assign_tk())) {
                check_end_of_theorem(m_p);
                m_value = m_p.save_pos(mk_expr_placeholder(), pos);
            } else {
                m_p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
                allow_nested_decls_scope scope2(is_definition());
                m_value = m_p.save_pos(m_p.parse_expr(), pos);
            }
        } else {
            buffer<expr> ps;
            optional<local_environment> lenv;
            bool last_block_delimited = false;
            lenv     = m_p.parse_binders(ps, last_block_delimited);
            auto pos = m_p.pos();
            if (m_p.curr_is_token(get_colon_tk())) {
                m_p.next();
                expr type  = m_p.parse_scoped_expr(ps, *lenv);
                m_type     = Pi(ps, type, m_p);
                save_checkpoint();
                add_meta_rec_ref();
                if (is_curr_with_or_comma_or_bar(m_p)) {
                    allow_nested_decls_scope scope2(is_definition());
                    m_value = parse_equations(m_p, m_name, type, m_aux_decls, lenv, ps, m_pos, is_meta());
                } else if (!is_definition() && !m_p.curr_is_token(get_assign_tk())) {
                    check_end_of_theorem(m_p);
                    m_value = m_p.save_pos(mk_expr_placeholder(), pos);
                } else {
                    allow_nested_decls_scope scope2(is_definition());
                    m_p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
                    m_value = m_p.parse_scoped_expr(ps, *lenv);
                }
            } else {
                if (!last_block_delimited && !ps.empty() &&
                    !is_placeholder(mlocal_type(ps.back()))) {
                    throw parser_error("invalid declaration, ambiguous parameter declaration, "
                                       "(solution: put parentheses around parameters)",
                                       pos);
                }
                m_type  = m_p.save_pos(mk_expr_placeholder(), m_p.pos());
                m_type  = Pi(ps, m_type, m_p);
                save_checkpoint();
                add_meta_rec_ref();
                m_p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
                allow_nested_decls_scope scope2(is_definition());
                m_value = m_p.parse_scoped_expr(ps, *lenv);
            }
            erase_local_binder_info(ps);
            m_value = Fun(ps, m_value, m_p);
        }
        m_end_pos = m_p.pos();
    }

    void mk_real_name() {
        if (m_is_private) {
            unsigned h  = hash(m_pos.first, m_pos.second);
            auto env_n  = add_private_name(m_env, m_name, optional<unsigned>(h));
            m_env       = env_n.first;
            m_real_name = env_n.second;
        } else if (m_kind == Example) {
            m_real_name = name("example");
        } else {
            name const & ns = get_namespace(m_env);
            m_real_name     = ns + m_name;
        }
    }

    void mk_aux_real_names() {
        if (m_is_private) {
            unsigned h  = hash(m_pos.first, m_pos.second);
            for (name const & aux : m_aux_decls) {
                auto env_n = add_private_name(m_env, aux, optional<unsigned>(h));
                m_env      = env_n.first;
                m_real_aux_names.push_back(env_n.second);
            }
        } else if (m_kind == Example) {
            // do nothing
        } else {
            name const & ns = get_namespace(m_env);
            for (name const & aux : m_aux_decls)
                m_real_aux_names.push_back(ns + aux);
        }
    }

    void parse() {
        parse_name();
        mk_real_name();
        parse_type_value();
        check_command_period_or_eof(m_p);
        if (m_p.used_sorry())
            m_p.declare_sorry();
        mk_aux_real_names();
        m_env = m_p.env();
    }

    void display_pos(std::ostream & out) {
        ::lean::display_pos(out, m_p.get_stream_name().c_str(), m_pos.first, m_pos.second);
    }

    certified_declaration check(declaration const & d) {
        if (m_p.profiling()) {
            std::ostringstream msg;
            display_pos(msg);
            msg << " type checking time for " << m_name;
            timeit timer(m_p.ios().get_diagnostic_stream(), msg.str().c_str(), LEAN_PROFILE_THRESHOLD);
            return ::lean::check(m_env, d);
        } else {
            return ::lean::check(m_env, d);
        }
    }

    void process_locals() {
        if (m_p.has_locals()) {
            buffer<expr> locals;
            collect_locals(m_type, m_value, m_p, locals);
            m_type = Pi_as_is(locals, m_type, m_p);
            buffer<expr> new_locals;
            new_locals.append(locals);
            erase_local_binder_info(new_locals);
            m_value = Fun_as_is(new_locals, m_value, m_p);
            auto ps = collect_univ_params_ignoring_tactics(m_type);
            ps      = collect_univ_params_ignoring_tactics(m_value, ps);
            update_univ_parameters(m_p, m_ls_buffer, ps);
            remove_local_vars(m_p, locals);
            m_ls = to_list(m_ls_buffer.begin(), m_ls_buffer.end());
            levels local_ls = collect_local_nonvar_levels(m_p, m_ls);
            local_ls = remove_local_vars(m_p, local_ls);
            if (!locals.empty()) {
                expr ref = mk_local_ref(m_real_name, local_ls, locals);
                m_env = m_p.add_local_ref(m_env, m_name, ref);
            } else if (local_ls) {
                expr ref = mk_constant(m_real_name, local_ls);
                m_env = m_p.add_local_ref(m_env, m_name, ref);
            }
        } else {
            update_univ_parameters(m_p, m_ls_buffer, collect_univ_params(m_value, collect_univ_params(m_type)));
            m_ls = to_list(m_ls_buffer.begin(), m_ls_buffer.end());
        }
    }

    bool try_cache() {
        // We don't cache examples.
        // We don't cache mutually recursive definitions (if this becomes a performance problem, we can fix it).
        if (m_kind != Example &&
            m_p.are_info_lines_valid(start_line(), end_line()) &&
            m_aux_decls.size() == 0) {
            // we only use the cache if the information associated with the line is valid
            if (auto it = m_p.find_cached_definition(m_real_name, m_type, m_value, is_trusted())) {
                optional<certified_declaration> cd;
                try {
                    level_param_names c_ls; expr c_type, c_value;
                    std::tie(c_ls, c_type, c_value) = *it;
                    // cache may have been created using a different trust level
                    c_type  = postprocess(m_env, c_type);
                    c_value = postprocess(m_env, c_value);
                    if (m_kind == Theorem) {
                        cd = check(mk_theorem(m_env, m_real_name, c_ls, c_type, c_value));
                        if (m_p.keep_new_thms()) {
                            if (!m_is_private)
                                m_p.add_decl_index(m_real_name, m_pos, m_p.get_cmd_token(), c_type);
                            m_p.add_delayed_theorem(*cd);
                        }
                        cd = check(mk_axiom(m_real_name, c_ls, c_type));
                        m_env = module::add(m_env, *cd);
                    } else {
                        c_value = extract_nested(c_value);
                        bool use_conv_opt = true;
                        cd = check(mk_definition(m_env, m_real_name, c_ls, c_type, c_value, use_conv_opt, is_trusted()));
                        if (!m_is_private)
                            m_p.add_decl_index(m_real_name, m_pos, m_p.get_cmd_token(), c_type);
                        m_env = module::add(m_env, *cd);
                    }
                    return true;
                } catch (exception&) {}
            }
        }
        return false;
    }

    void register_decl(name const & n, name const & real_n, expr const & type) {
        if (m_kind != Example) {
            if (!m_p.ignore_noncomputable()) {
                if (!m_is_noncomputable && is_marked_noncomputable(m_env, real_n)) {
                    auto reason = get_noncomputable_reason(m_env, real_n);
                    lean_assert(reason);
                    if (m_p.in_theorem_queue(*reason)) {
                        throw exception(sstream() << "definition '" << n << "' was marked as noncomputable because '" << *reason
                                        << "' is still in theorem queue (solution: use command 'reveal " << *reason << "'");
                    } else {
                        throw exception(sstream() << "definition '" << n
                                        << "' is noncomputable, it depends on '" << *reason << "'");
                    }
                }
                if (m_is_noncomputable && !is_marked_noncomputable(m_env, real_n)) {
                    throw exception(sstream() << "definition '" << n << "' was incorrectly marked as noncomputable");
                }
            }
            // TODO(Leo): register aux_decls
            if (!m_is_private) {
                m_p.add_decl_index(real_n, m_pos, m_p.get_cmd_token(), type);
                m_env = ensure_decl_namespaces(m_env, real_n);
            }
            if (m_is_protected)
                m_env = add_protected(m_env, real_n);
            if (n != real_n) {
                if (m_is_protected)
                    m_env = add_expr_alias_rec(m_env, get_protected_shortest_name(real_n), real_n);
                else
                    m_env = add_expr_alias_rec(m_env, n, real_n);
            }
            if (m_kind == Abbreviation || m_kind == LocalAbbreviation) {
                bool persistent = m_kind == Abbreviation;
                m_env = add_abbreviation(m_env, real_n, m_attributes.is_parsing_only(), persistent);
            }
            m_env = m_attributes.apply(m_env, m_p.ios(), real_n);
        }
    }

    void register_decl() {
        register_decl(m_name, m_real_name, m_type);
        for (unsigned i = 0; i < m_aux_decls.size(); i++) {
            register_decl(m_aux_decls[i], m_real_aux_names[i], m_aux_types[i]);
        }
    }

    // When compiling mutually recursive equations or equations based on well-found recursion,
    // the equations compiler produces a result that combines different definitions.
    // We say the result is "tangled". This method untangles it.
    // The tangled result is of the form
    //     Fun (a : A), [equations_result main-value aux-type-1 aux-value-1 ... aux-type-i aux-value-i]
    //
    // The result is the updated value. The auxiliary definitions (type and value) are stored at m_aux_types and aux_values
    expr untangle_definitions(expr const & type, expr const & value, buffer<expr> & aux_values) {
        if (is_lambda(value)) {
            lean_assert(is_pi(type));
            expr r = untangle_definitions(binding_body(type), binding_body(value), aux_values);
            lean_assert(aux_values.size() == m_aux_types.size());
            for (unsigned i = 0; i < aux_values.size(); i++) {
                m_aux_types[i] = mk_pi(binding_name(type), binding_domain(type), m_aux_types[i], binding_info(type));
                aux_values[i]  = mk_lambda(binding_name(value), binding_domain(value), aux_values[i], binding_info(value));
            }
            return update_binding(value, binding_domain(value), r);
        } else if (is_equations_result(value)) {
            lean_assert(get_equations_result_size(value) > 1);
            lean_assert(get_equations_result_size(value) % 2 == 1);
            for (unsigned i = 1; i < get_equations_result_size(value); i+=2) {
                m_aux_types.push_back(get_equations_result(value, i));
                aux_values.push_back(get_equations_result(value, i+1));
            }
            return get_equations_result(value, 0);
        } else {
            throw exception("invalid declaration, unexpected result produced by equations compiler");
        }
    }

    std::tuple<expr, level_param_names> elaborate_type(expr const & e) {
        bool clear_pre_info = false; // we don't want to clear pre_info data until we process the proof.
        if (m_p.profiling()) {
            std::ostringstream msg;
            display_pos(msg);
            msg << " type elaboration time for " << m_name;
            timeit timer(m_p.ios().get_diagnostic_stream(), msg.str().c_str(), LEAN_PROFILE_THRESHOLD);
            return m_p.old_elaborate_type(e, list<expr>(), clear_pre_info);
        } else {
            return m_p.old_elaborate_type(e, list<expr>(), clear_pre_info);
        }
    }

    std::tuple<expr, expr, level_param_names> elaborate_definition(expr const & type, expr const & value) {
        name const & def_name = m_kind == Example ? m_real_name : m_name;
        if (m_p.profiling()) {
            std::ostringstream msg;
            display_pos(msg);
            msg << " elaboration time for " << m_name;
            timeit timer(m_p.ios().get_diagnostic_stream(), msg.str().c_str(), LEAN_PROFILE_THRESHOLD);
            return m_p.old_elaborate_definition(def_name, type, value);
        } else {
            return m_p.old_elaborate_definition(def_name, type, value);
        }
    }

    // Elaborate definitions that contain auxiliary ones nested inside.
    // Remark: we do not cache this kind of definition.
    // This method will also initialize m_aux_types
    void elaborate_multi() {
        lean_assert(!m_aux_decls.empty());
        level_param_names new_ls;
        std::tie(m_type, m_value, new_ls) = elaborate_definition(m_type, m_value);
        new_ls = append(m_ls, new_ls);
        lean_assert(m_aux_types.empty());
        buffer<expr> aux_values;
        m_value = untangle_definitions(m_type, m_value, aux_values);
        lean_assert(aux_values.size() == m_aux_types.size());
        if (aux_values.size() != m_real_aux_names.size())
            throw exception("invalid declaration, failed to compile auxiliary declarations");
        m_type  = postprocess(m_env, m_type);
        m_value = extract_nested(postprocess(m_env, m_value));
        for (unsigned i = 0; i < aux_values.size(); i++) {
            m_aux_types[i] = postprocess(m_env, m_aux_types[i]);
            aux_values[i]  = postprocess(m_env, aux_values[i]);
        }
        if (is_definition()) {
            bool use_conv_opt = true;
            m_env = module::add(m_env, check(mk_definition(m_env, m_real_name, new_ls, m_type, m_value, use_conv_opt, is_trusted())));
            for (unsigned i = 0; i < aux_values.size(); i++)
                m_env = module::add(m_env, check(mk_definition(m_env, m_real_aux_names[i], new_ls,
                                                               m_aux_types[i], aux_values[i], use_conv_opt, is_trusted())));
        } else {
            m_env = module::add(m_env, check(mk_theorem(m_env, m_real_name, new_ls, m_type, m_value)));
            for (unsigned i = 0; i < aux_values.size(); i++)
                m_env = module::add(m_env, check(mk_theorem(m_env, m_real_aux_names[i], new_ls,
                                                            m_aux_types[i], aux_values[i])));
        }
    }

    void elaborate() {
        if (!try_cache()) {
            expr pre_type  = m_type;
            expr pre_value = m_value;
            level_param_names new_ls;
            m_p.remove_proof_state_info(m_pos, m_p.pos());
            if (!m_aux_decls.empty()) {
                // TODO(Leo): split equations_result
                elaborate_multi();
            } else if (!is_definition()) {
                // Theorems and Examples
                auto type_pos = m_p.pos_of(m_type);
                std::tie(m_type, new_ls) = elaborate_type(m_type);
                check_no_metavar(m_env, m_real_name, m_type, true);
                m_ls = append(m_ls, new_ls);
                m_type = postprocess(m_env, m_type);
                expr type_as_is = m_p.save_pos(mk_as_is(m_type), type_pos);
                if (!m_p.collecting_info() && !m_is_noncomputable && m_kind == Theorem && m_p.num_threads() > 1) {
                    // Add as axiom, and create a task to prove the theorem.
                    // Remark: we don't postpone the "proof" of Examples.
                    m_p.add_delayed_theorem(m_env, m_real_name, m_ls, type_as_is, m_value);
                    m_env = module::add(m_env, check(mk_axiom(m_real_name, m_ls, m_type)));
                } else {
                    std::tie(m_type, m_value, new_ls) = elaborate_definition(type_as_is, m_value);
                    m_type  = postprocess(m_env, m_type);
                    m_value = postprocess(m_env, m_value);
                    new_ls = append(m_ls, new_ls);
                    auto cd = is_example() ?
                        // Examples don't need to be trusted
                        check(mk_definition(m_env, m_real_name, new_ls, m_type, m_value, false, false))
                      : check(mk_theorem(m_env, m_real_name, new_ls, m_type, m_value));
                    if (m_kind == Theorem) {
                        // Remark: we don't keep examples
                        if (m_p.keep_new_thms()) {
                            m_p.add_delayed_theorem(cd);
                        }
                        cd = check(mk_axiom(m_real_name, new_ls, m_type));
                        m_env = module::add(m_env, cd);
                        m_p.cache_definition(m_real_name, pre_type, pre_value, new_ls, m_type, m_value, is_trusted());
                    }
                }
            } else {
                std::tie(m_type, m_value, new_ls) = elaborate_definition(m_type, m_value);
                new_ls       = append(m_ls, new_ls);
                m_type       = postprocess(m_env, m_type);
                m_value      = postprocess(m_env, m_value);
                expr new_val = extract_nested(m_value);
                bool use_conv_opt = true;
                m_env = module::add(m_env, check(mk_definition(m_env, m_real_name, new_ls, m_type, new_val, use_conv_opt, is_trusted())));
                // Remark: we cache the definition with the nested declarations.
                m_p.cache_definition(m_real_name, pre_type, pre_value, new_ls, m_type, m_value, is_trusted());
            }
        }
    }

    void process_as_axiom() {
        lean_assert(m_type_checkpoint);
        m_type      = *m_type_checkpoint;
        m_env       = *m_env_checkpoint;
        m_ls_buffer = m_ls_buffer_checkpoint;
        m_aux_decls.clear();
        m_real_aux_names.clear();

        expr dummy  = mk_Prop();
        m_value     = dummy;

        process_locals();
        mk_real_name();

        level_param_names new_ls;
        std::tie(m_type, new_ls) = elaborate_type(m_type);
        check_no_metavar(m_env, m_real_name, m_type, true);
        m_ls = append(m_ls, new_ls);
        m_type = postprocess(m_env, m_type);
        m_env = module::add(m_env, check(mk_axiom(m_real_name, m_ls, m_type)));
        register_decl(m_name, m_real_name, m_type);
    }

    void compile_decl() {
        if (m_is_noncomputable || !is_definition() || is_vm_builtin_function(m_real_name))
            return;
        try {
            declaration d = m_env.get(m_real_name);
            m_env         = vm_compile(m_env, d);
        } catch (exception & ext) {
            flycheck_warning wrn(m_p.ios());
            auto & out = m_p.ios().get_regular_stream();
            display_pos(out);
            out << "failed to generate bytecode for '" << m_real_name << "'" << std::endl;
            out << ext.what() << std::endl;
        }
    }

public:
    definition_cmd_fn(parser & p, def_cmd_kind kind, bool is_private, bool is_protected, bool is_noncomputable,
                      decl_attributes const & attributes):
        m_p(p), m_env(m_p.env()), m_kind(kind),
        m_is_private(is_private), m_is_protected(is_protected), m_is_noncomputable(is_noncomputable),
        m_pos(p.pos()), m_attributes(attributes) {
        lean_assert(!(m_is_private && m_is_protected));
        if (!is_standard(m_p.env()) && is_noncomputable)
            throw exception("invalid 'noncomputable' declarations, it can only be used in the standard library");
        if (kind != Definition && is_noncomputable)
            throw exception("invalid 'noncomputable' declaration, it can only be used for definitions");
    }

    environment operator()() {
        try {
            parse();
            process_locals();
            elaborate();
            register_decl();
            compile_decl();
            return m_env;
        } catch (exception & ex) {
            if (m_type_checkpoint) {
                try {
                    process_as_axiom();
                } catch (exception & ex2) {
                    ex.rethrow();
                }
                throw update_environment_exception(m_env, std::shared_ptr<throwable>(ex.clone()));
            }
            ex.rethrow();
            lean_unreachable();
        }
    }
};

static environment definition_cmd_core(parser & p, def_cmd_kind kind, bool is_private, bool is_protected, bool is_noncomputable,
                                       decl_attributes const & attributes) {
    return definition_cmd_fn(p, kind, is_private, is_protected, is_noncomputable, attributes)();
}
environment local_abbreviation_cmd(parser & p) {
    return definition_cmd_core(p, LocalAbbreviation, true, false, false, {});
}
static environment example_cmd(parser & p) {
    definition_cmd_core(p, Example, false, false, false, {});
    return p.env();
}

static environment definition_cmd_ex(parser & p, decl_attributes const & attributes) {
    bool is_private   = false;
    bool is_protected = false;
    if (p.curr_is_token(get_private_tk())) {
        is_private = true;
        p.next();

        if (!attributes && p.curr_is_token(get_structure_tk())) {
            return structure_cmd_ex(p, attributes, true);
        }
    } else if (p.curr_is_token(get_protected_tk())) {
        is_protected = true;
        p.next();

        if (!attributes) {
            if (p.curr_is_token_or_id(get_axiom_tk())) {
                p.next();
                return variable_cmd_core(p, variable_kind::Axiom, true);
            } else if (p.curr_is_token_or_id(get_constant_tk())) {
                p.next();
                return variable_cmd_core(p, variable_kind::Constant, true);
            } else if (p.curr_is_token_or_id(get_meta_constant_tk())) {
                p.next();
                return variable_cmd_core(p, variable_kind::MetaConstant, true);
            } else if (p.curr_is_token_or_id(get_axioms_tk())) {
                p.next();
                return variables_cmd_core(p, variable_kind::Axiom, true);
            } else if (p.curr_is_token_or_id(get_constants_tk())) {
                p.next();
                return variables_cmd_core(p, variable_kind::Constant, true);
            }
        }
    }

    bool is_noncomputable = false;
    if (p.curr_is_token(get_noncomputable_tk())) {
        is_noncomputable = true;
        p.next();

        if (!attributes && !is_private && !is_protected && p.curr_is_token_or_id(get_theory_tk())) {
            p.next();
            p.set_ignore_noncomputable();
            return p.env();
        }
    }

    def_cmd_kind kind = Definition;
    if (p.curr_is_token_or_id(get_definition_tk())) {
        p.next();
    } else if (p.curr_is_token_or_id(get_meta_definition_tk())) {
        kind = MetaDefinition;
        p.next();
    } else if (p.curr_is_token_or_id(get_abbreviation_tk())) {
        kind = Abbreviation;
        p.next();
    } else if (p.curr_is_token_or_id(get_theorem_tk())) {
        p.next();
        kind = Theorem;
    } else if (p.curr_is_token_or_id(get_mutual_definition_tk())) {
        p.next();
        return mutual_definition_cmd_core(p, Definition, is_private, is_protected, is_noncomputable, attributes);
    } else if (p.curr_is_token_or_id(get_mutual_meta_definition_tk())) {
        p.next();
        return mutual_definition_cmd_core(p, MetaDefinition, is_private, is_protected, is_noncomputable, attributes);
    } else {
        throw parser_error("invalid definition/theorem, 'definition' or 'theorem' expected", p.pos());
    }
    if (p.use_new_elaborator())
        return xdefinition_cmd_core(p, kind, is_private, is_protected, is_noncomputable, attributes);
    else
        return definition_cmd_core(p, kind, is_private, is_protected, is_noncomputable, attributes);
}

static environment definition_cmd(parser & p) {
    return definition_cmd_ex(p, {});
}

static environment include_cmd_core(parser & p, bool include) {
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

static environment include_cmd(parser & p) {
    return include_cmd_core(p, true);
}

static environment omit_cmd(parser & p) {
    return include_cmd_core(p, false);
}

static environment attribute_cmd_core(parser & p, bool persistent) {
    buffer<name> ds;
    decl_attributes attributes(persistent);
    bool parsed_attrs = false;
    if (!p.curr_is_identifier()) {
        attributes.parse(p);
        parsed_attrs  = true;
        // 'attribute [attr] definition ...'
        if (p.curr_is_command()) {
            if (p.curr_is_token_or_id(get_inductive_tk())) {
                return inductive_cmd_ex(p, attributes);
            } else if (p.curr_is_token_or_id(get_mutual_inductive_tk())) {
                return mutual_inductive_cmd_ex(p, attributes);
            } else  if (p.curr_is_token_or_id(get_structure_tk())) {
                return structure_cmd_ex(p, attributes, false);
            } else {
                return definition_cmd_ex(p, attributes);
            }
        }
    }
    name d          = p.check_constant_next("invalid 'attribute' command, constant expected");
    ds.push_back(d);
    while (p.curr_is_identifier()) {
        ds.push_back(p.check_constant_next("invalid 'attribute' command, constant expected"));
    }
    if (!parsed_attrs)
        attributes.parse(p);
    if (attributes.is_parsing_only())
        throw exception(sstream() << "invalid [parsing_only] attribute, can only be applied at declaration time");
    environment env = p.env();
    for (name const & d : ds)
        env = attributes.apply(env, p.ios(), d);
    return env;
}

static environment attribute_cmd(parser & p) {
    return attribute_cmd_core(p, true);
}

environment local_attribute_cmd(parser & p) {
    return attribute_cmd_core(p, false);
}

static environment reveal_cmd(parser & p) {
    buffer<name> ds;
    name d          = p.check_constant_next("invalid 'reveal' command, constant expected");
    ds.push_back(d);
    while (p.curr_is_identifier()) {
        ds.push_back(p.check_constant_next("invalid 'reveal' command, constant expected"));
    }
    return p.reveal_theorems(ds);
}

void register_decl_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("universe",        "declare a universe level", universe_cmd));
    add_cmd(r, cmd_info("universes",       "declare universe levels", universes_cmd));
    add_cmd(r, cmd_info("variable",        "declare a new variable", variable_cmd));
    add_cmd(r, cmd_info("parameter",       "declare a new parameter", parameter_cmd));
    add_cmd(r, cmd_info("constant",        "declare a new constant (aka top-level variable)", constant_cmd));
    add_cmd(r, cmd_info("meta_constant",   "declare a new meta constant", meta_constant_cmd));
    add_cmd(r, cmd_info("axiom",           "declare a new axiom", axiom_cmd));
    add_cmd(r, cmd_info("variables",       "declare new variables", variables_cmd));
    add_cmd(r, cmd_info("parameters",      "declare new parameters", parameters_cmd));
    add_cmd(r, cmd_info("constants",       "declare new constants (aka top-level variables)", constants_cmd));
    add_cmd(r, cmd_info("axioms",          "declare new axioms", axioms_cmd));
    add_cmd(r, cmd_info("definition",      "add new definition", definition_cmd, false));
    add_cmd(r, cmd_info("meta_definition", "add new meta definition", definition_cmd, false));
    add_cmd(r, cmd_info("noncomputable",   "add new noncomputable definition", definition_cmd, false));
    add_cmd(r, cmd_info("example",         "add new example", example_cmd));
    add_cmd(r, cmd_info("private",         "add new private definition/theorem", definition_cmd, false));
    add_cmd(r, cmd_info("protected",       "add new protected definition/theorem/variable", definition_cmd, false));
    add_cmd(r, cmd_info("theorem",         "add new theorem", definition_cmd, false));
    add_cmd(r, cmd_info("reveal",          "reveal given theorems", reveal_cmd));
    add_cmd(r, cmd_info("include",         "force section parameter/variable to be included", include_cmd));
    add_cmd(r, cmd_info("attribute",       "set declaration attributes", attribute_cmd));
    add_cmd(r, cmd_info("abbreviation",    "declare a new abbreviation", definition_cmd, false));
    add_cmd(r, cmd_info("omit",            "undo 'include' command", omit_cmd));
    add_cmd(r, cmd_info("mutual_definition",      "declare a mutually recursive definition", definition_cmd, false));
    add_cmd(r, cmd_info("mutual_meta_definition", "declare a mutually recursive meta_definition", definition_cmd, false));
}

void initialize_decl_cmds() {
}
void finalize_decl_cmds() {
}
}
