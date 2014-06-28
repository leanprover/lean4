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
#include "kernel/free_vars.h"
#include "library/scoped_ext.h"
#include "library/locals.h"
#include "library/placeholder.h"
#include "library/aliases.h"
#include "library/explicit.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/util.h"
#include "frontends/lean/parser.h"

namespace lean {
static name g_assign(":=");
static name g_with("with");
static name g_colon(":");
static name g_bar("|");
static name g_lcurly("{");
static name g_rcurly("}");

using inductive::intro_rule;
using inductive::inductive_decl;
using inductive::inductive_decl_name;
using inductive::inductive_decl_type;
using inductive::inductive_decl_intros;
using inductive::intro_rule_name;
using inductive::intro_rule_type;

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
        if (is_not_zero(r))
            return r;
        else
            return impredicative ? mk_max(r, mk_level_one()) : r;
    }
}

static expr update_result_sort(type_checker & tc, expr t, level const & l) {
    t = tc.whnf(t);
    if (is_pi(t)) {
        return update_binding(t, binding_domain(t), update_result_sort(tc, binding_body(t), l));
    } else if (is_sort(t)) {
        return update_sort(t, l);
    } else {
        lean_unreachable();
    }
}

/** \brief Return the universe level of the given inductive datatype declaration. */
level get_datatype_result_level(type_checker & tc, inductive_decl const & d) {
    expr d_t = tc.whnf(inductive_decl_type(d));
    while (is_pi(d_t)) {
        d_t = tc.whnf(binding_body(d_t));
    }
    if (!is_sort(d_t)) {
        std::cout << "ERROR: " << inductive_decl_type(d) << "\n";
        throw exception(sstream() << "invalid inductive datatype '" << inductive_decl_name(d) << "', "
                        "resultant type is not a sort");
    }
    return sort_level(d_t);
}

/** \brief Return true if \c u occurs in \c l */
bool occurs(level const & u, level const & l) {
    bool found = false;
    for_each(l, [&](level const & l) {
            if (found) return false;
            if (l == u) { found = true; return false; }
            return true;
        });
    return found;
}

static name g_tmp_prefix = name::mk_internal_unique_name();
/**
   \brief Given a type \c t for an introduction rule, store the universe of the types of non-parameters in \c ls.

   \remark aux_u is an temporary universe used for inductive decls. It should be ignored.
*/
static void accumulate_levels(type_checker & tc, expr t, unsigned num_params, level const & aux_u, buffer<level> & ls) {
    name_generator ngen(g_tmp_prefix);
    unsigned i = 0;
    while (is_pi(t)) {
        if (i >= num_params) {
            expr s  = tc.ensure_type(binding_domain(t));
            level l = sort_level(s);
            if (l == aux_u) {
                // ignore, this is the auxiliary level
            } else if (occurs(aux_u, l)) {
                throw exception("failed to infer inductive datatype resultant universe, provide the universe levels explicitly");
            } else if (std::find(ls.begin(), ls.end(), l) == ls.end()) {
                ls.push_back(l);
            }
        }
        t = instantiate(binding_body(t), mk_local(ngen.next(), binding_name(t), binding_domain(t)));
        i++;
    }
}

void throw_all_or_nothing() {
    throw exception("invalid mutually recursive datatype declaration, "
                    "if the universe level of one type is provided, then all of them should be");
}

static void elaborate_inductive(buffer<inductive_decl> & decls, level_param_names const & lvls, unsigned num_params, parser & p) {
    // temporary environment used during elaboration
    environment env = p.env();
    // add fake universe level
    name u_name(g_tmp_prefix, "u");
    env = env.add_universe(u_name);
    level u = mk_global_univ(u_name);
    std::unique_ptr<type_checker> tc(new type_checker(env));
    bool infer_result_universe = false;
    unsigned first = true;
    // elaborate inductive datatype types, and declare them in temporary environment.
    for (inductive_decl & d : decls) {
        level l = get_datatype_result_level(*tc, d);
        expr  t = inductive_decl_type(d);
        if (is_placeholder(l)) {
            if (first)
                infer_result_universe  = true;
            else if (!infer_result_universe)
                throw_all_or_nothing();
            t = update_result_sort(*tc, t, u);
        } else if (!first && infer_result_universe) {
            throw_all_or_nothing();
        }
        t = p.elaborate(env, t);
        env = env.add(check(env, mk_var_decl(inductive_decl_name(d), lvls, t)));
        d = inductive_decl(inductive_decl_name(d), t, inductive_decl_intros(d));
        first = false;
    }
    tc.reset(new type_checker(env));
    buffer<level> r_lvls; // used for inferring the universe level of resultant datatypes.
    // elaborate introduction rules using temporary environment
    for (inductive_decl & d : decls) {
        buffer<intro_rule> intros;
        for (intro_rule const & ir : inductive_decl_intros(d)) {
            expr t = p.elaborate(env, intro_rule_type(ir));
            if (infer_result_universe)
                accumulate_levels(*tc, t, num_params, u, r_lvls);
            intros.push_back(intro_rule(intro_rule_name(ir), t));
        }
        d = inductive_decl(inductive_decl_name(d), inductive_decl_type(d), to_list(intros.begin(), intros.end()));
    }
    if (infer_result_universe) {
        level r_lvl = normalize(mk_result_level(env.impredicative(), r_lvls));
        for (inductive_decl & d : decls) {
            expr t = inductive_decl_type(d);
            t = update_result_sort(*tc, t, r_lvl);
            d = inductive_decl(inductive_decl_name(d), t, inductive_decl_intros(d));
        }
    }
}

static environment create_alias(environment const & env, name const & full_id, name const & id, levels const & section_leves,
                                buffer<parameter> const & section_params, parser & p) {
    if (in_section(env)) {
        expr r = mk_explicit(mk_constant(full_id, section_leves));
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
    // store intro rule name that are markes for relaxed implicit argument inference.
    name_set               relaxed_implicit_inference;
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
        // parse introduction rules
        p.check_token_next(g_assign, "invalid inductive declaration, ':=' expected");
        buffer<intro_rule> intros;
        while (p.curr_is_token(g_bar)) {
            p.next();
            name intro_id = p.check_id_next("invalid introduction rule, identifier expected");
            check_atomic(intro_id);
            name full_intro_id = ns + intro_id;
            id_to_short_id.insert(full_intro_id, intro_id);
            bool strict = true;
            if (p.curr_is_token(g_lcurly)) {
                p.next();
                p.check_token_next(g_rcurly, "invalid introduction rule, '}' expected");
                strict = false;
                relaxed_implicit_inference.insert(full_intro_id);
            }
            p.check_token_next(g_colon, "invalid introduction rule, ':' expected");
            expr intro_type = p.parse_scoped_expr(ps, lenv);
            intro_type = p.pi_abstract(ps, intro_type);
            intro_type = infer_implicit(intro_type, ps.size(), strict);
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
    // Add section_params to introduction rules type, and also "fix"
    // occurrences of inductive types.
    for (inductive_decl & d : decls) {
        buffer<intro_rule> new_irs;
        for (auto const & ir : inductive_decl_intros(d)) {
            expr type = intro_rule_type(ir);
            type = fix_inductive_occs(type, decls, ls_buffer, section_params);
            type = p.pi_abstract(section_params, type);
            bool strict = relaxed_implicit_inference.contains(intro_rule_name(ir));
            type = infer_implicit(type, section_params.size(), strict);
            new_irs.push_back(intro_rule(intro_rule_name(ir), type));
        }
        d = inductive_decl(inductive_decl_name(d),
                           inductive_decl_type(d),
                           to_list(new_irs.begin(), new_irs.end()));
    }
    num_params += section_params.size();
    level_param_names ls = to_list(ls_buffer.begin(), ls_buffer.end());

    elaborate_inductive(decls, ls, num_params, p);
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
