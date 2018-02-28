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
#include "library/unfold_macros.h"
#include "library/documentation.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/definition_cmds.h"
#include "frontends/lean/inductive_cmds.h"
#include "frontends/lean/info_manager.h"

namespace lean {
// TODO(Leo): delete
void update_univ_parameters(parser & p, buffer<name> & lp_names, name_set const & found);

static environment declare_universe(parser & p, environment env, name const & n, bool local) {
    if (local) {
        p.add_local_level(n, mk_param_univ(n), local);
    } else if (in_section(env)) {
        p.add_local_level(n, mk_param_univ(n), false);
    } else {
        p.add_local_level(n, mk_param_univ(n), true);
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

enum class variable_kind { Constant, Parameter, Variable, Axiom };

static void check_parameter_type(parser & p, name const & n, expr const & type, pos_info const & pos) {
    for_each(type, [&](expr const & e, unsigned) {
            if (is_local(e) && p.is_local_variable(e))
                throw parser_error(sstream() << "invalid parameter declaration '" << n << "', it depends on " <<
                                   "variable '" << mlocal_pp_name(e) << "'", pos);
            return true;
        });
}

static environment declare_var(parser & p, environment env,
                               name const & n, level_param_names const & ls, expr const & type,
                               variable_kind k, optional<binder_info> const & _bi, pos_info const & pos,
                               cmd_meta const & meta) {
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
        name u = p.next_name();
        expr l = p.save_pos(mk_local(u, n, type, bi), pos);
        if (k == variable_kind::Parameter)
            p.add_parameter(n, l);
        else
            p.add_variable(n, l);
        return env;
    } else {
        lean_assert(k == variable_kind::Constant || k == variable_kind::Axiom);
        name const & ns = get_namespace(env);
        name full_n  = ns + n;

        buffer<name> new_ls;
        to_buffer(ls, new_ls);
        buffer<expr> new_params;
        collect_implicit_locals(p, new_ls, new_params, type);
        expr new_type = Pi(new_params, type);
        new_type = unfold_untrusted_macros(env, new_type);

        if (k == variable_kind::Axiom) {
            env = module::add(env, check(env, mk_axiom(full_n, ls, new_type)));
        } else {
            bool is_trusted = !meta.m_modifiers.m_is_meta;
            env = module::add(env, check(env, mk_constant_assumption(full_n, ls, new_type, is_trusted)));
        }
        if (meta.m_doc_string)
            env = add_doc_string(env, full_n, *meta.m_doc_string);
        if (!ns.is_anonymous()) {
            if (meta.m_modifiers.m_is_protected)
                env = add_expr_alias(env, get_protected_shortest_name(full_n), full_n);
            else
                env = add_expr_alias(env, n, full_n);
        }
        if (meta.m_modifiers.m_is_protected)
            env = add_protected(env, full_n);
        env = ensure_decl_namespaces(env, full_n);
        /* Apply attributes last so that they may access any information on the new decl */
        env = meta.m_attrs.apply(env, p.ios(), full_n);
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
        if (p.is_local_variable_user_name(n))
            throw parser_error(sstream() << "invalid parameter binder type update, '"
                               << n << "' is a variable", pos);
        if (!p.update_local_binder_info(n, new_bi))
            throw parser_error(sstream() << "invalid parameter binder type update, '"
                               << n << "' is not a parameter", pos);
    } else {
        if (!p.update_local_binder_info(n, new_bi) || !p.is_local_variable_user_name(n))
            throw parser_error(sstream() << "invalid variable binder type update, '"
                               << n << "' is not a variable", pos);
    }
}

static bool curr_is_binder_annotation(parser & p) {
    return p.curr_is_token(get_lparen_tk()) || p.curr_is_token(get_lcurly_tk()) ||
           p.curr_is_token(get_ldcurly_tk()) || p.curr_is_token(get_lbracket_tk());
}

/* Auxiliary class to setup naming scopes for a variable/parameter/constant/axiom command.

   We need the private_name_scope because the type may contain match-expressions.
   These match expressions produce private definitions, and we need to make sure
   they use the same infrastructure we use for definitions/theorems.
*/
class var_decl_scope {
    environment m_env;
    declaration_info_scope m_info_scope;
    private_name_scope     m_prv_scope;
public:
    var_decl_scope(parser & p, decl_modifiers const & mods):
        m_env(p.env()),
        m_info_scope(p, decl_cmd_kind::Var, mods),
        m_prv_scope(true, m_env) {
        p.set_env(m_env);
    }
};

static environment variable_cmd_core(parser & p, variable_kind k, cmd_meta const & meta) {
    check_variable_kind(p, k);
    auto pos = p.pos();
    module::scope_pos_info scope_pos(pos);
    optional<binder_info> bi;
    if (k == variable_kind::Parameter || k == variable_kind::Variable)
        bi = parse_binder_info(p, k);
    optional<parser::local_scope> scope1;
    name n;
    expr type;
    buffer<name> ls_buffer;
    if (bi && bi->is_inst_implicit() && (k == variable_kind::Parameter || k == variable_kind::Variable)) {
        var_decl_scope var_scope(p, meta.m_modifiers);
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
                /*
                  annotation update: variable [decA]
                  or
                  parameter-less anonymous local instance : variable [io.interface]
                */
                auto it = p.get_local(n);
                if (it && is_local(*it)) {
                    // annotation update: variable [decA]
                    p.parse_close_binder_info(bi);
                    update_local_binder_info(p, k, n, bi, pos);
                    return p.env();
                } else {
                    // parameter-less anonymous local instance : variable [io.interface]
                    type = p.id_to_expr(n, n_pos);
                    n    = p.mk_anonymous_inst_name();
                }
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
        var_decl_scope var_scope(p, meta.m_modifiers);
        /* non instance implicit cases */
        if (p.curr_is_token(get_lcurly_tk()) && (k == variable_kind::Parameter || k == variable_kind::Variable))
            throw parser_error("invalid declaration, only constants/axioms can be universe polymorphic", p.pos());
        if (k == variable_kind::Constant || k == variable_kind::Axiom)
            scope1.emplace(p);
        parse_univ_params(p, ls_buffer);
        n = p.check_decl_id_next("invalid declaration, identifier expected");
        if (!p.curr_is_token(get_colon_tk())) {
            if (!curr_is_binder_annotation(p) && (k == variable_kind::Parameter || k == variable_kind::Variable)) {
                p.parse_close_binder_info(bi);
                update_local_binder_info(p, k, n, bi, pos);
                return p.env();
            } else {
                buffer<expr> ps;
                unsigned rbp = 0;
                bool allow_default = true;
                auto lenv = p.parse_binders(ps, rbp, allow_default);
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
    check_command_period_docstring_or_eof(p);
    level_param_names ls;
    if (ls_buffer.empty()) {
        ls = to_level_param_names(collect_univ_params(type));
    } else {
        update_univ_parameters(p, ls_buffer, collect_univ_params(type));
        ls = to_list(ls_buffer.begin(), ls_buffer.end());
    }
    level_param_names new_ls;
    list<expr> ctx = p.locals_to_context();
    std::tie(type, new_ls) = p.elaborate_type("_variable", ctx, type);
    if (k == variable_kind::Variable || k == variable_kind::Parameter)
        update_local_levels(p, new_ls, k == variable_kind::Variable);
    return declare_var(p, p.env(), n, append(ls, new_ls), type, k, bi, pos, meta);
}
static environment variable_cmd(parser & p, cmd_meta const & meta) {
    return variable_cmd_core(p, variable_kind::Variable, meta);
}
static environment axiom_cmd(parser & p, cmd_meta const & meta)    {
    if (meta.m_modifiers.m_is_meta)
        throw exception("invalid 'meta' modifier for axiom");
    return variable_cmd_core(p, variable_kind::Axiom, meta);
}
static environment constant_cmd(parser & p, cmd_meta const & meta)    {
    return variable_cmd_core(p, variable_kind::Constant, meta);
}
static environment parameter_cmd(parser & p, cmd_meta const & meta)    {
    return variable_cmd_core(p, variable_kind::Parameter, meta);
}

/*
Remark: we currently do not support declarations such as:

  parameters P Q : match ... end

User should use

  parameter P : match ... end
  parameter Q : match ... end

instead.
*/
static void ensure_no_match_in_variables_cmd(pos_info const & pos) {
    if (used_match_idx()) {
        throw parser_error("match-expressions are not supported in `parameters/variables/constants` commands "
                           "(solution use `parameter/variable/constant` commands)", pos);
    }
}

static environment variables_cmd_core(parser & p, variable_kind k, cmd_meta const & meta) {
    check_variable_kind(p, k);
    auto pos = p.pos();
    module::scope_pos_info scope_pos(pos);
    declaration_info_scope d_scope(p, decl_cmd_kind::Var, meta.m_modifiers);
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
                ensure_no_match_in_variables_cmd(pos);
            } else if (p.curr_is_token(get_rbracket_tk())) {
                /* annotation update: variables [decA] */
                p.parse_close_binder_info(bi);
                update_local_binder_info(p, k, id, bi, pos);
                if (curr_is_binder_annotation(p))
                    return variables_cmd_core(p, k, meta);
                else
                    return p.env();
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
                ensure_no_match_in_variables_cmd(pos);
            }
        } else {
            /* anonymous : variables [forall x y, decidable (x = y)] */
            name id = p.mk_anonymous_inst_name();
            ids.push_back(id);
            type = p.parse_expr();
            ensure_no_match_in_variables_cmd(pos);
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
                    return variables_cmd_core(p, k, meta);
                else
                    return p.env();
            } else {
                throw parser_error("invalid variables/constants/axioms declaration, ':' expected", pos);
            }
        }
        if (k == variable_kind::Constant || k == variable_kind::Axiom)
            scope1.emplace(p);
        type = p.parse_expr();
        ensure_no_match_in_variables_cmd(pos);
    }
    p.parse_close_binder_info(bi);
    environment env = p.env();
    level_param_names ls = to_level_param_names(collect_univ_params(type));
    list<expr> ctx = p.locals_to_context();
    for (auto id : ids) {
        // Hack: to make sure we get different universe parameters for each parameter.
        // Alternative: elaborate once and copy types replacing universes in new_ls.
        level_param_names new_ls;
        expr new_type;
        check_command_period_open_binder_or_eof(p);
        std::tie(new_type, new_ls) = p.elaborate_type("_variables", ctx, type);
        if (k == variable_kind::Variable || k == variable_kind::Parameter)
            update_local_levels(p, new_ls, k == variable_kind::Variable);
        new_ls = append(ls, new_ls);
        env = declare_var(p, env, id, new_ls, new_type, k, bi, pos, meta);
    }
    if (curr_is_binder_annotation(p)) {
        if (k == variable_kind::Constant || k == variable_kind::Axiom) {
            // Hack: temporarily update the parser environment.
            // We must do that to be able to process
            //    constants (A : Type) (a : A)
            parser::local_scope scope2(p, env);
            return variables_cmd_core(p, k, meta);
        } else {
            return variables_cmd_core(p, k, meta);
        }
    }
    return env;
}
static environment variables_cmd(parser & p, cmd_meta const & meta) {
    return variables_cmd_core(p, variable_kind::Variable, meta);
}
static environment parameters_cmd(parser & p, cmd_meta const & meta) {
    return variables_cmd_core(p, variable_kind::Parameter, meta);
}
static environment constants_cmd(parser & p, cmd_meta const & meta) {
    return variables_cmd_core(p, variable_kind::Constant, meta);
}
static environment axioms_cmd(parser & p, cmd_meta const & meta) {
    return variables_cmd_core(p, variable_kind::Axiom, meta);
}

static environment definition_cmd(parser & p, cmd_meta const & meta) {
    return definition_cmd_core(p, decl_cmd_kind::Definition, meta);
}
static environment theorem_cmd(parser & p, cmd_meta const & meta) {
    return definition_cmd_core(p, decl_cmd_kind::Theorem, meta);
}
static environment abbreviation_cmd(parser & p, cmd_meta const & meta) {
    return definition_cmd_core(p, decl_cmd_kind::Abbreviation, meta);
}
static environment example_cmd(parser & p, cmd_meta const & meta) {
    return definition_cmd_core(p, decl_cmd_kind::Example, meta);
}
static environment instance_cmd(parser & p, cmd_meta const & _meta) {
    auto meta = _meta;
    if (meta.m_modifiers.m_is_private)
        throw exception("invalid 'private' modifier for instance command");
    if (meta.m_modifiers.m_is_protected)
        throw exception("invalid 'protected' modifier for instance command");
    if (meta.m_modifiers.m_is_mutual)
        throw exception("invalid 'mutual' modifier for instance command");
    meta.m_modifiers.m_is_protected = true;
    return definition_cmd_core(p, decl_cmd_kind::Instance, meta);
}

static environment modifiers_cmd(parser & p, cmd_meta const & _meta) {
    auto meta = _meta;
    if (p.curr_is_token(get_private_tk())) {
        meta.m_modifiers.m_is_private = true;
        p.next();
    } else if (p.curr_is_token(get_protected_tk())) {
        meta.m_modifiers.m_is_protected = true;
        p.next();
    }

    if (p.curr_is_token(get_noncomputable_tk())) {
        p.next();
        if (!meta.m_attrs && !meta.m_modifiers && p.curr_is_token_or_id(get_theory_tk())) {
            // `noncomputable theory`
            p.next();
            p.set_ignore_noncomputable();
            return p.env();
        } else {
            meta.m_modifiers.m_is_noncomputable = true;
        }
    }
    if (p.curr_is_token(get_meta_tk())) {
        meta.m_modifiers.m_is_meta = true;
        p.next();
    }

    if (p.curr_is_token(get_mutual_tk())) {
        meta.m_modifiers.m_is_mutual = true;
        p.next();
    }

    if (p.curr_is_token(get_private_tk()) || p.curr_is_token(get_protected_tk()) || p.curr_is_token(get_noncomputable_tk())
        || p.curr_is_token(get_meta_tk()) || p.curr_is_token(get_mutual_tk())) {
        throw parser_error("unexpected definition modifier", p.pos());
    }
    if (p.curr_is_token(get_attribute_tk()) || p.curr_is_token("@[")) {
        throw parser_error("unexpected attributes declaration", p.pos());
    }
    p.parse_command(meta);
    return p.env();
}

static environment attribute_cmd_core(parser & p, bool persistent) {
    buffer<name> ds;
    decl_attributes attributes(persistent);
    attributes.parse(p);
    // 'attribute [attr] definition ...'
    if (p.curr_is_command()) {
        return modifiers_cmd(p, {attributes, {}, {}});
    }
    do {
        auto pos = p.pos();
        name d = p.check_constant_next("invalid 'attribute' command, constant expected");
        ds.push_back(d);
        if (get_global_info_manager())
            get_global_info_manager()->add_const_info(p.env(), pos, d);
    } while (p.curr_is_identifier());
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

static environment compact_attribute_cmd(parser & p, cmd_meta const & meta) {
    bool persistent = true;
    decl_attributes attributes(persistent);
    attributes.parse_compact(p);
    return modifiers_cmd(p, {attributes, meta.m_modifiers, meta.m_doc_string});
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

void register_decl_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("universe",        "declare a universe level", universe_cmd));
    add_cmd(r, cmd_info("universes",       "declare universe levels", universes_cmd));
    add_cmd(r, cmd_info("variable",        "declare a new variable", variable_cmd));
    add_cmd(r, cmd_info("parameter",       "declare a new parameter", parameter_cmd));
    add_cmd(r, cmd_info("constant",        "declare a new constant (aka top-level variable)", constant_cmd));
    add_cmd(r, cmd_info("axiom",           "declare a new axiom", axiom_cmd));
    add_cmd(r, cmd_info("variables",       "declare new variables", variables_cmd));
    add_cmd(r, cmd_info("parameters",      "declare new parameters", parameters_cmd));
    add_cmd(r, cmd_info("constants",       "declare new constants (aka top-level variables)", constants_cmd));
    add_cmd(r, cmd_info("axioms",          "declare new axioms", axioms_cmd));
    add_cmd(r, cmd_info("meta",            "add new meta declaration", modifiers_cmd, false));
    add_cmd(r, cmd_info("mutual",          "add new mutual declaration", modifiers_cmd, false));
    add_cmd(r, cmd_info("noncomputable",   "add new noncomputable definition", modifiers_cmd, false));
    add_cmd(r, cmd_info("private",         "add new private declaration", modifiers_cmd, false));
    add_cmd(r, cmd_info("protected",       "add new protected declaration", modifiers_cmd, false));
    add_cmd(r, cmd_info("definition",      "add new definition", definition_cmd));
    add_cmd(r, cmd_info("theorem",         "add new theorem", theorem_cmd));
    add_cmd(r, cmd_info("instance",        "add new instance", instance_cmd));
    add_cmd(r, cmd_info("abbreviation",    "add new abbreviation", abbreviation_cmd));
    add_cmd(r, cmd_info("example",         "add new example", example_cmd));
    add_cmd(r, cmd_info("include",         "force section parameter/variable to be included", include_cmd));
    add_cmd(r, cmd_info("attribute",       "set declaration attributes", attribute_cmd));
    add_cmd(r, cmd_info("@[",              "declaration attributes", compact_attribute_cmd));
    add_cmd(r, cmd_info("omit",            "undo 'include' command", omit_cmd));
}

void initialize_decl_cmds() {
}
void finalize_decl_cmds() {
}
}
