/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <algorithm>
#include "runtime/sstream.h"
#include "util/fresh_name.h"
#include "util/timeit.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "library/aliases.h"
#include "library/private.h"
#include "library/protected.h"
#include "library/placeholder.h"
#include "library/locals.h"
#include "library/explicit.h"
#include "library/compiler/compiler.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/definition_cmds.h"
#include "frontends/lean/inductive_cmds.h"
#include "frontends/lean/decl_cmds.h"

namespace lean {
// TODO(Leo): delete
void update_univ_parameters(parser & p, buffer<name> & lp_names, name_set const & found);

static environment declare_universe(parser & p, environment env, name const & n, bool local) {
    if (local) {
        p.add_local_level(n, mk_univ_param(n), local);
    } else if (in_section(env)) {
        p.add_local_level(n, mk_univ_param(n), false);
    } else {
        p.add_local_level(n, mk_univ_param(n), true);
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
        bool local = true;
        if (p.curr_is_token(get_variable_tk())) {
            p.next();
            local = true;
        }
        name n = p.check_decl_id_next("invalid 'universe' command, identifier expected");
        return declare_universe(p, p.env(), n, local);
    }
}

static environment universes_cmd(parser & p) {
    return universes_cmd_core(p, true);
}

static environment declare_var(parser & p, environment env,
                               name const & n, names const & ls, expr const & type,
                               variable_kind k, optional<binder_info> const & _bi, pos_info const & pos,
                               cmd_meta const & meta) {
    binder_info bi;
    if (_bi) bi = *_bi; else bi = mk_binder_info();
    if (k == variable_kind::Variable) {
        if (p.get_local(n))
            throw parser_error(sstream() << "invalid variable declaration, '"
                               << n << "' has already been declared", pos);
        name u = p.next_name();
        expr l = p.save_pos(mk_local(u, n, type, bi), pos);
        p.add_variable(n, l);
        return env;
    } else {
        name const & ns = get_namespace(env);
        name full_n  = ns + n;

        buffer<name> new_ls;
        to_buffer(ls, new_ls);
        buffer<expr> new_params;
        collect_implicit_locals(p, new_ls, new_params, type);
        expr new_type = Pi(new_params, type);

        bool is_unsafe = meta.m_modifiers.m_is_unsafe;
        env = env.add(mk_axiom(full_n, ls, new_type, is_unsafe));

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
        env = meta.m_attrs.apply_all(env, p.ios(), full_n);
        return env;
    }
}

/** \brief If we are in a section, then add the new local levels to it. */
static void update_local_levels(parser & p, names const & new_ls, bool is_variable) {
    for (auto const & l : new_ls)
        p.add_local_level(l, mk_univ_param(l), is_variable);
}

optional<binder_info> parse_binder_info(parser & p, variable_kind k) {
    optional<binder_info> bi = p.parse_optional_binder_info();
    if (bi && k != variable_kind::Variable)
        parser_error("invalid binder annotation, it can only be used to declare variables", p.pos());
    return bi;
}

static void check_variable_kind(parser & p, variable_kind k) {
    if (in_section(p.env())) {
        if (k == variable_kind::Axiom)
            throw parser_error("invalid declaration, 'axiom' cannot be used in sections",
                               p.pos());
    }
}

static void update_local_binder_info(parser & p, variable_kind /* k */, name const & n,
                                     optional<binder_info> const & bi, pos_info const & pos) {
    binder_info new_bi;
    if (bi) new_bi = *bi; else new_bi = mk_binder_info();
    if (!p.update_local_binder_info(n, new_bi) || !p.is_local_variable_user_name(n))
        throw parser_error(sstream() << "invalid variable binder type update, '"
                           << n << "' is not a variable", pos);
}

static bool curr_is_binder_annotation(parser & p) {
    return p.curr_is_token(get_lparen_tk()) || p.curr_is_token(get_lcurly_tk()) ||
           p.curr_is_token(get_ldcurly_tk()) || p.curr_is_token(get_lbracket_tk());
}

/* Auxiliary class to setup naming scopes for a variable/axiom command.

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

environment elab_var(parser & p, variable_kind const & k, cmd_meta const & meta, pos_info const & pos,
                     optional<binder_info> const & bi, name const & n, expr type, buffer<name> & ls_buffer) {
    names ls;
    if (ls_buffer.empty()) {
        ls = to_names(collect_univ_params(type));
    } else {
        update_univ_parameters(p, ls_buffer, collect_univ_params(type));
        ls = names(ls_buffer);
    }
    names new_ls;
    list<expr> ctx = p.locals_to_context();
    std::tie(type, new_ls) = p.elaborate_type("_variable", ctx, type);
    if (k == variable_kind::Variable)
        update_local_levels(p, new_ls, k == variable_kind::Variable);
    return declare_var(p, p.env(), n, append(ls, new_ls), type, k, bi, pos, meta);
}

static environment variable_cmd_core(parser & p, variable_kind k, cmd_meta const & meta) {
    check_variable_kind(p, k);
    auto pos = p.pos();
    optional<binder_info> bi;
    if (k == variable_kind::Variable)
        bi = parse_binder_info(p, k);
    optional<parser::local_scope> scope1;
    name n;
    expr type;
    buffer<name> ls_buffer;
    if (bi && is_inst_implicit(*bi) && (k == variable_kind::Variable)) {
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
        if (p.curr_is_token(get_lcurly_tk()) && (k == variable_kind::Variable))
            throw parser_error("invalid declaration, only axioms can be universe polymorphic", p.pos());
        if (k == variable_kind::Axiom)
            scope1.emplace(p);
        parse_univ_params(p, ls_buffer);
        n = p.check_decl_id_next("invalid declaration, identifier expected");
        if (!p.curr_is_token(get_colon_tk())) {
            if (!curr_is_binder_annotation(p) && (k == variable_kind::Variable)) {
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
    return elab_var(p, k, meta, pos, bi, n,
                    type, ls_buffer);
}
static environment variable_cmd(parser & p, cmd_meta const & meta) {
    return variable_cmd_core(p, variable_kind::Variable, meta);
}
static environment axiom_cmd(parser & p, cmd_meta const & meta)    {
    return variable_cmd_core(p, variable_kind::Axiom, meta);
}

/*
Remark: we currently do not support declarations such as:

  variables P Q : match ... end

User should use

  variable P : match ... end
  variable Q : match ... end

instead.
*/
static void ensure_no_match_in_variables_cmd(pos_info const & pos) {
    if (used_match_idx()) {
        throw parser_error("match-expressions are not supported in `variables` commands", pos);
    }
}

static environment variables_cmd_core(parser & p, variable_kind k, cmd_meta const & meta) {
    check_variable_kind(p, k);
    auto pos = p.pos();
    declaration_info_scope d_scope(p, decl_cmd_kind::Var, meta.m_modifiers);
    optional<binder_info> bi = parse_binder_info(p, k);
    buffer<name> ids;
    optional<parser::local_scope> scope1;
    expr type;
    if (bi && is_inst_implicit(*bi) && (k == variable_kind::Variable)) {
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
            if (k == variable_kind::Variable) {
                p.parse_close_binder_info(bi);
                for (name const & id : ids) {
                    update_local_binder_info(p, k, id, bi, pos);
                }
                if (curr_is_binder_annotation(p))
                    return variables_cmd_core(p, k, meta);
                else
                    return p.env();
            } else {
                throw parser_error("invalid variables declaration, ':' expected", pos);
            }
        }
        if (k == variable_kind::Axiom)
            scope1.emplace(p);
        type = p.parse_expr();
        ensure_no_match_in_variables_cmd(pos);
    }
    p.parse_close_binder_info(bi);
    environment env = p.env();
    names ls = to_names(collect_univ_params(type));
    list<expr> ctx = p.locals_to_context();
    for (auto id : ids) {
        // Hack: to make sure we get different universe parameters for each parameter.
        // Alternative: elaborate once and copy types replacing universes in new_ls.
        names new_ls;
        expr new_type;
        check_command_period_open_binder_or_eof(p);
        std::tie(new_type, new_ls) = p.elaborate_type("_variables", ctx, type);
        if (k == variable_kind::Variable)
            update_local_levels(p, new_ls, k == variable_kind::Variable);
        new_ls = append(ls, new_ls);
        env = declare_var(p, env, id, new_ls, new_type, k, bi, pos, meta);
    }
    if (curr_is_binder_annotation(p)) {
        return variables_cmd_core(p, k, meta);
    }
    return env;
}
static environment variables_cmd(parser & p, cmd_meta const & meta) {
    return variables_cmd_core(p, variable_kind::Variable, meta);
}
static environment definition_cmd(parser & p, cmd_meta const & meta) {
    return definition_cmd_core(p, decl_cmd_kind::Definition, meta);
}
static environment theorem_cmd(parser & p, cmd_meta const & meta) {
    return definition_cmd_core(p, decl_cmd_kind::Theorem, meta);
}
static environment constant_cmd(parser & p, cmd_meta const & meta) {
    return definition_cmd_core(p, decl_cmd_kind::OpaqueConst, meta);
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

    if (p.curr_is_token(get_unsafe_tk())) {
        meta.m_modifiers.m_is_unsafe = true;
        p.next();
    }

    if (p.curr_is_token(get_partial_tk())) {
        meta.m_modifiers.m_is_partial = true;
        p.next();
    }

    if (p.curr_is_token(get_mutual_tk())) {
        meta.m_modifiers.m_is_mutual = true;
        p.next();
    }

    if (p.curr_is_token(get_private_tk()) || p.curr_is_token(get_protected_tk()) || p.curr_is_token(get_noncomputable_tk())
        || p.curr_is_token(get_unsafe_tk()) || p.curr_is_token(get_mutual_tk())) {
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
        name d = p.check_constant_next("invalid 'attribute' command, constant expected");
        ds.push_back(d);
    } while (p.curr_is_identifier());
    environment env = p.env();
    for (name const & d : ds)
        env = attributes.apply_all(env, p.ios(), d);
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

void register_decl_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("universe",        "declare a universe level", universe_cmd));
    add_cmd(r, cmd_info("universes",       "declare universe levels", universes_cmd));
    add_cmd(r, cmd_info("variable",        "declare a new variable", variable_cmd));
    add_cmd(r, cmd_info("constant",        "declare a new constant (aka top-level variable)", constant_cmd));
    add_cmd(r, cmd_info("variables",       "declare new variables", variables_cmd));
    add_cmd(r, cmd_info("axiom",           "declare a new axiom", axiom_cmd));
    add_cmd(r, cmd_info("unsafe",          "add new unsafe declaration", modifiers_cmd, false));
    add_cmd(r, cmd_info("partial",         "add new partial declaration", modifiers_cmd, false));
    add_cmd(r, cmd_info("mutual",          "add new mutual declaration", modifiers_cmd, false));
    add_cmd(r, cmd_info("noncomputable",   "add new noncomputable definition", modifiers_cmd, false));
    add_cmd(r, cmd_info("private",         "add new private declaration", modifiers_cmd, false));
    add_cmd(r, cmd_info("protected",       "add new protected declaration", modifiers_cmd, false));
    add_cmd(r, cmd_info("def",             "add new definition", definition_cmd));
    add_cmd(r, cmd_info("theorem",         "add new theorem", theorem_cmd));
    add_cmd(r, cmd_info("instance",        "add new instance", instance_cmd));
    add_cmd(r, cmd_info("abbreviation",    "add new abbreviation", abbreviation_cmd));
    add_cmd(r, cmd_info("abbrev",          "add new abbreviation", abbreviation_cmd));
    add_cmd(r, cmd_info("example",         "add new example", example_cmd));
    add_cmd(r, cmd_info("attribute",       "set declaration attributes", attribute_cmd));
    add_cmd(r, cmd_info("@[",              "declaration attributes", compact_attribute_cmd));
}

void initialize_decl_cmds() {
}
void finalize_decl_cmds() {
}
}
