/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "util/name_map.h"
#include "kernel/replace_fn.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/scoped_ext.h"
#include "library/locals.h"
#include "library/placeholder.h"
#include "library/aliases.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/util.h"
#include "frontends/lean/parser.h"

namespace lean {
static name g_assign(":=");
static name g_with("with");
static name g_colon(":");
static name g_bar("|");

using inductive::intro_rule;
using inductive::inductive_decl;
using inductive::inductive_decl_name;
using inductive::inductive_decl_type;
using inductive::inductive_decl_intros;
using inductive::intro_rule_name;
using inductive::intro_rule_type;

// Mark all parameters as implicit
static void make_implicit(buffer<parameter> & ps) {
    for (parameter & p : ps)
        p.m_bi = mk_implicit_binder_info();
}

// Make sure that every inductive datatype (in decls) occurring in \c type has
// the universe levels \c lvl_params and section parameters \c section_params
static expr fix_inductive_occs(expr const & type, buffer<inductive_decl> const & decls,
                               buffer<name> const & lvl_params, buffer<parameter> const & section_params) {
    return replace(type, [&](expr const & e, unsigned) {
            if (!is_constant(e))
                return none_expr();
            if (!std::any_of(decls.begin(), decls.end(),
                             [&](inductive_decl const & d) { return const_name(e) == inductive_decl_name(d); }))
                return none_expr();
            // found target
            levels  ls = const_levels(e);
            unsigned n = length(ls);
            if (n < lvl_params.size()) {
                unsigned i = lvl_params.size() - n;
                while (i > 0) {
                    --i;
                    ls = cons(mk_param_univ(lvl_params[i]), ls);
                }
            }
            expr r = update_constant(e, ls);
            for (unsigned i = 0; i < section_params.size(); i++)
                r = mk_app(r, section_params[i].m_local);
            return some_expr(r);
        });
}

static level mk_result_level(bool impredicative, buffer<level> const & ls) {
    if (ls.empty()) {
        return impredicative ? mk_level_one() : mk_level_zero();
    } else {
        level r = ls[0];
        for (unsigned i = 1; i < ls.size(); i++)
            r = mk_max(r, ls[i]);
        return impredicative ? mk_max(r, mk_level_one()) : r;
    }
}

static expr update_result_sort(expr const & t, level const & l) {
    if (is_pi(t)) {
        return update_binding(t, binding_domain(t), update_result_sort(binding_body(t), l));
    } else if (is_sort(t)) {
        return update_sort(t, l);
    } else {
        lean_unreachable();
    }
}

static name g_tmp_prefix = name::mk_internal_unique_name();
static void set_result_universes(buffer<inductive_decl> & decls, level_param_names const & lvls, unsigned num_params, parser & p) {
    if (std::all_of(decls.begin(), decls.end(), [](inductive_decl const & d) {
                return !has_placeholder(inductive_decl_type(d));
            }))
        return; // nothing to be done
    // We can't infer the type of intro rule arguments because we did declare the inductive datatypes.
    // So, we use the following trick, we create a "draft" environment where the inductive datatypes
    // are asserted as variable declarations, and keep doing that until we reach a "fix" point.
    unsigned num_rounds = 0;
    while (true) {
        if (num_rounds > 2*decls.size() + 1) {
            // TODO(Leo): this is test is a hack to avoid non-termination.
            // We should use a better termination condition
            throw exception("failed to compute resultant universe level for inductive datatypes, "
                            "provide explicit universe levels");
        }
        num_rounds++;
        bool progress = false;
        environment env    = p.env();
        bool impredicative = env.impredicative();
        // first assert inductive types that do not have placeholders
        for (auto const & d : decls) {
            expr type = inductive_decl_type(d);
            if (!has_placeholder(type))
                env = env.add(check(env, mk_var_decl(inductive_decl_name(d), lvls, inductive_decl_type(d))));
        }
        type_checker   tc(env);
        name_generator ngen(g_tmp_prefix);
        // try to update resultant universe levels
        for (auto & d : decls) {
            expr d_t = inductive_decl_type(d);
            while (is_pi(d_t)) {
                d_t = binding_body(d_t);
            }
            if (!is_sort(d_t))
                throw exception(sstream() << "invalid inductive datatype '" << inductive_decl_name(d) << "', "
                                "resultant type is not a sort");
            level r_lvl = sort_level(d_t);
            if (impredicative && is_zero(r_lvl))
                continue;
            buffer<level>  lvls;
            for (intro_rule const & ir : inductive_decl_intros(d)) {
                expr t     = intro_rule_type(ir);
                unsigned i = 0;
                while (is_pi(t)) {
                    if (i >= num_params) {
                        try {
                            expr s = tc.ensure_type(binding_domain(t));
                            level lvl = sort_level(s);
                            if (std::find(lvls.begin(), lvls.end(), lvl) == lvls.end())
                                lvls.push_back(lvl);
                        } catch (...) {
                        }
                    }
                    t = instantiate(binding_body(t), mk_local(ngen.next(), binding_name(t), binding_domain(t)));
                    i++;
                }
            }
            level m_lvl = normalize(mk_result_level(impredicative, lvls));
            if (is_placeholder(r_lvl) || !(is_geq(r_lvl, m_lvl))) {
                progress = true;
                // update result level
                expr new_type = update_result_sort(inductive_decl_type(d), m_lvl);
                d = inductive_decl(inductive_decl_name(d), new_type, inductive_decl_intros(d));
            }
        }
        if (!progress)
            break;
    }
}

static environment create_alias(environment const & env, name const & full_id, name const & id, levels const & section_leves,
                                buffer<parameter> const & section_params, parser & p) {
    if (in_section(env)) {
        expr r = mark_explicit(mk_constant(full_id, section_leves));
        for (unsigned i = 0; i < section_params.size(); i++)
            r = mk_app(r, section_params[i].m_local);
        p.add_local_expr(id, r);
        return env;
    } else if (full_id != id) {
        return add_alias(env, id, mk_constant(full_id));
    } else {
        return env;
    }
}

environment inductive_cmd(parser & p) {
    parser::no_undef_id_error_scope err_scope(p);
    environment            env = p.env();
    name const &           ns = get_namespace(env);
    bool                   first = true;
    buffer<name>           ls_buffer;
    name_map<name>         id_to_short_id;
    unsigned               num_params = 0;
    bool                   explicit_levels = false;
    buffer<inductive_decl> decls;
    while (true) {
        parser::local_scope l_scope(p);
        auto id_pos  = p.pos();
        name id      = p.check_id_next("invalid inductive declaration, identifier expected");
        check_atomic(id);
        name full_id = ns + id;
        id_to_short_id.insert(full_id, id);
        buffer<name> curr_ls_buffer;
        expr type;
        optional<parser::param_universe_scope> pu_scope;
        if (parse_univ_params(p, curr_ls_buffer)) {
            if (first) {
                explicit_levels = true;
                ls_buffer.append(curr_ls_buffer);
            } else if (!explicit_levels) {
                throw parser_error("invalid mutually recursive declaration, "
                                   "explicit universe levels were not provided for previous inductive types in this declaration",
                                   id_pos);
            } else if (curr_ls_buffer.size() != ls_buffer.size()) {
                throw parser_error("invalid mutually recursive declaration, "
                                   "all inductive types must have the same number of universe paramaters", id_pos);
            } else {
                for (unsigned i = 0; i < ls_buffer.size(); i++) {
                    if (curr_ls_buffer[i] != ls_buffer[i])
                        throw parser_error("invalid mutually recursive inductive declaration, "
                                           "all inductive types must have the same universe paramaters", id_pos);
                }
            }
        } else {
            if (first) {
                explicit_levels = false;
            } else if (explicit_levels)  {
                throw parser_error("invalid mutually recursive declaration, "
                                   "explicit universe levels were provided for previous inductive types in this declaration",
                                   id_pos);
            }
            // initialize param_universe_scope, we are using implicit universe levels
            pu_scope.emplace(p);
        }
        buffer<parameter> ps;
        local_environment lenv = env;
        auto params_pos = p.pos();
        if (!p.curr_is_token(g_colon)) {
            lenv = p.parse_binders(ps);
            p.check_token_next(g_colon, "invalid inductive declaration, ':' expected");
            {
                parser::placeholder_universe_scope place_scope(p);
                type = p.parse_scoped_expr(ps, lenv);
            }
            type = p.pi_abstract(ps, type);
        } else {
            p.next();
            parser::placeholder_universe_scope place_scope(p);
            type = p.parse_scoped_expr(ps, lenv);
        }
        // check if number of parameters
        if (first) {
            num_params = ps.size();
        } else {
            // mutually recursive declaration checks
            if (num_params != ps.size()) {
                throw parser_error("invalid mutually recursive inductive declaration, "
                                   "all inductive types must have the same number of arguments",
                                   params_pos);
            }
        }
        make_implicit(ps); // parameters are implicit for introduction rules
        // parse introduction rules
        p.check_token_next(g_assign, "invalid inductive declaration, ':=' expected");
        buffer<intro_rule> intros;
        while (p.curr_is_token(g_bar)) {
            p.next();
            name intro_id = p.check_id_next("invalid introduction rule, identifier expected");
            check_atomic(intro_id);
            name full_intro_id = ns + intro_id;
            id_to_short_id.insert(full_intro_id, intro_id);
            p.check_token_next(g_colon, "invalid introduction rule, ':' expected");
            expr intro_type = p.parse_scoped_expr(ps, lenv);
            intro_type = p.pi_abstract(ps, intro_type);
            intros.push_back(intro_rule(full_intro_id, intro_type));
        }
        decls.push_back(inductive_decl(full_id, type, to_list(intros.begin(), intros.end())));
        if (!p.curr_is_token(g_with))
            break;
        p.next();
        first = false;
    }
    // Collect (section) locals occurring in inductive_decls, and abstract them
    // using these additional parameters.
    name_set used_levels;
    name_set section_locals;
    for (inductive_decl const & d : decls) {
        used_levels    = collect_univ_params(inductive_decl_type(d), used_levels);
        section_locals = collect_locals(inductive_decl_type(d), section_locals);
        for (auto const & ir : inductive_decl_intros(d)) {
            used_levels    = collect_univ_params(intro_rule_type(ir), used_levels);
            section_locals = collect_locals(intro_rule_type(ir), section_locals);
        }
    }
    update_univ_parameters(ls_buffer, used_levels, p);
    buffer<parameter> section_params;
    mk_section_params(section_locals, p, section_params);
    // First, add section_params to inductive types type.
    // We don't update the introduction rules in the first pass, because
    // we will mark all section_params as implicit for them.
    for (inductive_decl & d : decls) {
        d = inductive_decl(inductive_decl_name(d),
                           p.pi_abstract(section_params, inductive_decl_type(d)),
                           inductive_decl_intros(d));
    }
    make_implicit(section_params);
    // Add section_params to introduction rules type, and also "fix"
    // occurrences of inductive types.
    for (inductive_decl & d : decls) {
        buffer<intro_rule> new_irs;
        for (auto const & ir : inductive_decl_intros(d)) {
            expr type = intro_rule_type(ir);
            type = fix_inductive_occs(type, decls, ls_buffer, section_params);
            type = p.pi_abstract(section_params, type);
            new_irs.push_back(intro_rule(intro_rule_name(ir), type));
        }
        d = inductive_decl(inductive_decl_name(d),
                           inductive_decl_type(d),
                           to_list(new_irs.begin(), new_irs.end()));
    }
    num_params += section_params.size();
    level_param_names ls = to_list(ls_buffer.begin(), ls_buffer.end());

    // Check if introduction rules do not have placeholders
    for (inductive_decl const & d : decls) {
        for (auto const & ir : inductive_decl_intros(d)) {
            if (has_placeholder(intro_rule_type(ir)))
                throw exception(sstream() << "invalid inductive datatype '" << inductive_decl_name(d) << "', "
                                << "introduction rule '" << intro_rule_name(ir) << "' has placeholders");
        }
    }
    // "Fix" the inductive type resultant type universe level, if it was not explicitly provided.
    set_result_universes(decls, ls, num_params, p);
    env = module::add_inductive(env, ls, num_params, to_list(decls.begin(), decls.end()));
    // Create aliases/local refs
    levels section_levels = collect_section_levels(ls, p);
    for (inductive_decl const & d : decls) {
        name const & n = inductive_decl_name(d);
        env = create_alias(env, n, *id_to_short_id.find(n), section_levels, section_params, p);
        env = create_alias(env, n.append_after("_rec"), id_to_short_id.find(n)->append_after("_rec"), section_levels, section_params, p);
        for (intro_rule const & ir : inductive_decl_intros(d)) {
            name const & n = intro_rule_name(ir);
            env = create_alias(env, n, *id_to_short_id.find(n), section_levels, section_params, p);
        }
    }
    return env;
}
void register_inductive_cmd(cmd_table & r) {
    add_cmd(r, cmd_info("inductive",   "declare an inductive datatype", inductive_cmd));
}
}
