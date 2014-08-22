/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/sstream.h"
#include "util/name_map.h"
#include "kernel/replace_fn.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "kernel/abstract.h"
#include "kernel/free_vars.h"
#include "library/scoped_ext.h"
#include "library/locals.h"
#include "library/placeholder.h"
#include "library/aliases.h"
#include "library/explicit.h"
#include "library/opaque_hints.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/util.h"
#include "frontends/lean/parser.h"

namespace lean {
static name g_assign(":=");
static name g_with("with");
static name g_colon(":");
static name g_comma(",");
static name g_lcurly("{");
static name g_rcurly("}");

using inductive::intro_rule;
using inductive::inductive_decl;
using inductive::inductive_decl_name;
using inductive::inductive_decl_type;
using inductive::inductive_decl_intros;
using inductive::intro_rule_name;
using inductive::intro_rule_type;

inductive_decl update_inductive_decl(inductive_decl const & d, expr const & t) {
    return inductive_decl(inductive_decl_name(d), t, inductive_decl_intros(d));
}

inductive_decl update_inductive_decl(inductive_decl const & d, buffer<intro_rule> const & irs) {
    return inductive_decl(inductive_decl_name(d), inductive_decl_type(d), to_list(irs.begin(), irs.end()));
}

intro_rule update_intro_rule(intro_rule const & r, expr const & t) {
    return intro_rule(intro_rule_name(r), t);
}

static name g_tmp_prefix = name::mk_internal_unique_name();

struct inductive_cmd_fn {
    typedef std::unique_ptr<type_checker> type_checker_ptr;
    parser &         m_p;
    environment      m_env;
    type_checker_ptr m_tc;
    name             m_namespace; // current namespace
    pos_info         m_pos; // current position for reporting errors
    bool             m_first; // true if parsing the first inductive type in a mutually recursive inductive decl.
    buffer<name>     m_explict_levels;
    buffer<name>     m_levels;
    bool             m_using_explicit_levels; // true if the user is providing explicit universe levels
    unsigned         m_num_params; // number of parameters
    level            m_u; // temporary auxiliary global universe used for inferring the result universe of an inductive datatype declaration.
    bool             m_infer_result_universe;
    name_set         m_relaxed_implicit_infer; // set of introduction rules where we do not use strict implicit parameter infererence

    inductive_cmd_fn(parser & p):m_p(p) {
        m_env   = p.env();
        m_first = true;
        m_using_explicit_levels = false;
        m_num_params = 0;
        name u_name(g_tmp_prefix, "u");
        m_env = m_env.add_universe(u_name);
        m_u = mk_global_univ(u_name);
        m_infer_result_universe = false;
        m_namespace = get_namespace(m_env);
        m_tc = mk_type_checker_with_hints(m_env, m_p.mk_ngen(), false);
    }

    [[ noreturn ]] void throw_error(char const * error_msg) { throw parser_error(error_msg, m_pos); }
    [[ noreturn ]] void throw_error(sstream const & strm) { throw parser_error(strm, m_pos); }

    name mk_rec_name(name const & n) {
        return n.append_after("_rec");
    }

    /** \brief Parse the name of an inductive datatype or introduction rule,
        prefix the current namespace to it and return it.
    */
    name parse_decl_name(bool is_intro) {
        m_pos   = m_p.pos();
        name id = m_p.check_id_next("invalid declaration, identifier expected");
        check_atomic(id);
        name full_id = m_namespace + id;
        m_p.add_decl_index(full_id, m_pos);
        if (!is_intro)
            m_p.add_decl_index(mk_rec_name(full_id), m_pos);
        return full_id;
    }

    name parse_inductive_decl_name() { return parse_decl_name(false); }
    name parse_intro_decl_name() { return parse_decl_name(true); }

    /** \brief Parse inductive declaration universe parameters.
        If this is the first declaration in a mutually recursive block, then this method
        stores the levels in m_explict_levels, and set m_using_explicit_levels to true (iff they were provided).

        If this is not the first declaration, then this function just checks if the parsed parameters
        match the ones in the first declaration (stored in \c m_explict_levels)
    */
    void parse_inductive_univ_params() {
        buffer<name> curr_ls_buffer;
        if (parse_univ_params(m_p, curr_ls_buffer)) {
            if (m_first) {
                m_using_explicit_levels = true;
                m_explict_levels.append(curr_ls_buffer);
            } else if (!m_using_explicit_levels) {
                throw_error("invalid mutually recursive declaration, "
                            "explicit universe levels were not provided for previous inductive types in this declaration");
            } else if (curr_ls_buffer.size() != m_explict_levels.size()) {
                throw_error("invalid mutually recursive declaration, "
                            "all inductive types must have the same number of universe paramaters");
            } else {
                for (unsigned i = 0; i < m_explict_levels.size(); i++) {
                    if (curr_ls_buffer[i] != m_explict_levels[i])
                        throw_error("invalid mutually recursive inductive declaration, "
                                    "all inductive types must have the same universe paramaters");
                }
            }
        } else {
            if (m_first) {
                m_using_explicit_levels = false;
            } else if (m_using_explicit_levels) {
                throw_error("invalid mutually recursive declaration, "
                            "explicit universe levels were provided for previous inductive types in this declaration");
            }
        }
    }

    /** \brief Parse the type of an inductive datatype */
    expr parse_datatype_type() {
        expr type;
        buffer<expr> ps;
        m_pos = m_p.pos();
        if (m_p.curr_is_token(g_assign)) {
            type = mk_sort(mk_level_placeholder());
        } else if (!m_p.curr_is_token(g_colon)) {
            m_p.parse_binders(ps);
            if (m_p.curr_is_token(g_colon)) {
                m_p.next();
                type = m_p.parse_scoped_expr(ps);
            } else {
                type = mk_sort(mk_level_placeholder());
            }
            type = Pi(ps, type, m_p);
        } else {
            m_p.next();
            type = m_p.parse_expr();
        }
        // check if number of parameters
        if (m_first) {
            m_num_params = ps.size();
        } else if (m_num_params != ps.size()) {
            // mutually recursive declaration checks
            throw_error("invalid mutually recursive inductive declaration, all inductive types must have the same number of arguments");
        }
        return type;
    }

    /** \brief Return the universe level of the given type, if it is not a sort, then raise an exception. */
    level get_datatype_result_level(expr d_type) {
        d_type = m_tc->whnf(d_type).first;
        while (is_pi(d_type)) {
            d_type = m_tc->whnf(binding_body(d_type)).first;
        }
        if (!is_sort(d_type))
            throw_error(sstream() << "invalid inductive datatype, resultant type is not a sort");
        return sort_level(d_type);
    }

    /** \brief Update the result sort of the given type */
    expr update_result_sort(expr t, level const & l) {
        t = m_tc->whnf(t).first;
        if (is_pi(t)) {
            return update_binding(t, binding_domain(t), update_result_sort(binding_body(t), l));
        } else if (is_sort(t)) {
            return update_sort(t, l);
        } else {
            lean_unreachable();
        }
    }

    /** \brief Elaborate the type of an inductive declaration. */
    std::tuple<expr, level_param_names> elaborate_inductive_type(expr d_type) {
        level l = get_datatype_result_level(d_type);
        if (is_placeholder(l)) {
            if (m_using_explicit_levels)
                throw_error("resultant universe must be provided, when using explicit universe levels");
            d_type = update_result_sort(d_type, m_u);
            m_infer_result_universe = true;
        }
        return m_p.elaborate_at(m_env, d_type);
    }

    /** \brief Create a local constant based on the given binding */
    expr mk_local_for(expr const & b) {
        return mk_local(m_p.mk_fresh_name(), binding_name(b), binding_domain(b), binding_info(b));
    }

    /** \brief Check if the parameters of \c d_type and \c first_d_type are equal. */
    void check_params(expr d_type, expr first_d_type) {
        for (unsigned i = 0; i < m_num_params; i++) {
            if (!m_tc->is_def_eq(binding_domain(d_type), binding_domain(first_d_type)).first)
                throw_error(sstream() << "invalid parameter #" << (i+1) << " in mutually recursive inductive declaration, "
                            << "all inductive types must have equivalent parameters");
            expr l = mk_local_for(d_type);
            d_type       = instantiate(binding_body(d_type), l);
            first_d_type = instantiate(binding_body(first_d_type), l);
        }
    }

    /** \brief Check if the level names in d_lvls and \c first_d_lvls are equal. */
    void check_levels(level_param_names d_lvls, level_param_names first_d_lvls) {
        while (!is_nil(d_lvls) && !is_nil(first_d_lvls)) {
            if (head(d_lvls) != head(first_d_lvls))
                throw_error(sstream() << "invalid mutually recursive inductive declaration, "
                            << "all declarations must use the same universe parameter names, mismatch: '"
                            << head(d_lvls) << "' and '" << head(first_d_lvls) << "' "
                            << "(if the universe parameters were inferred, then provide them explicitly to fix the problem)");
            d_lvls       = tail(d_lvls);
            first_d_lvls = tail(first_d_lvls);
        }
        if (!is_nil(d_lvls) || !is_nil(first_d_lvls))
            throw_error("invalid mutually recursive inductive declaration, "
                        "all declarations must have the same number of arguments "
                        "(this is error is probably due to inferred implicit parameters, provide all parameters explicitly to fix the problem");
    }

    /** \brief Add the parameters of the inductive decl type to the local scoped.
        This method is executed before parsing introduction rules.
    */
    void add_params_to_local_scope(expr d_type, buffer<expr> & params) {
        for (unsigned i = 0; i < m_num_params; i++) {
            expr l = mk_local_for(d_type);
            m_p.add_local(l);
            params.push_back(l);
            d_type = instantiate(binding_body(d_type), l);
        }
    }

    /** \brief Parse introduction rules in the scope of the given parameters.
        Introduction rules with the annotation '{}' are marked for relaxed (aka non-strict) implicit parameter inference.
    */
    list<intro_rule> parse_intro_rules(buffer<expr> & params) {
        buffer<intro_rule> intros;
        while (true) {
            name intro_name = parse_intro_decl_name();
            bool strict = true;
            if (m_p.curr_is_token(g_lcurly)) {
                m_p.next();
                m_p.check_token_next(g_rcurly, "invalid introduction rule, '}' expected");
                strict = false;
                m_relaxed_implicit_infer.insert(intro_name);
            }
            m_p.check_token_next(g_colon, "invalid introduction rule, ':' expected");
            expr intro_type = m_p.parse_scoped_expr(params, m_env);
            intro_type = Pi(params, intro_type, m_p);
            intro_type = infer_implicit(intro_type, params.size(), strict);
            intros.push_back(intro_rule(intro_name, intro_type));
            if (!m_p.curr_is_token(g_comma))
                break;
            m_p.next();
        }
        return to_list(intros.begin(), intros.end());
    }

    void parse_inductive_decls(buffer<inductive_decl> & decls) {
        optional<expr> first_d_type;
        optional<level_param_names> first_d_lvls;
        while (true) {
            parser::local_scope l_scope(m_p);
            name d_name = parse_inductive_decl_name();
            parse_inductive_univ_params();
            expr d_type = parse_datatype_type();
            bool empty_type = true;
            if (m_p.curr_is_token(g_assign)) {
                empty_type = false;
                m_p.next();
            }
            level_param_names d_lvls;
            std::tie(d_type, d_lvls) = elaborate_inductive_type(d_type);
            if (!m_first) {
                check_params(d_type, *first_d_type);
                check_levels(d_lvls, *first_d_lvls);
            }
            if (empty_type) {
                decls.push_back(inductive_decl(d_name, d_type, list<intro_rule>()));
            } else {
                buffer<expr> params;
                add_params_to_local_scope(d_type, params);
                auto d_intro_rules = parse_intro_rules(params);
                decls.push_back(inductive_decl(d_name, d_type, d_intro_rules));
            }
            if (!m_p.curr_is_token(g_with)) {
                m_levels.append(m_explict_levels);
                for (auto l : d_lvls) m_levels.push_back(l);
                break;
            }
            m_p.next();
            m_first = false;
            first_d_type = d_type;
            first_d_lvls = d_lvls;
        }
    }

    /** \brief Include in m_levels any section level referenced by decls. */
    void include_section_levels(buffer<inductive_decl> const & decls) {
        if (!in_section(m_env))
            return;
        name_set all_lvl_params;
        for (auto const & d : decls) {
            all_lvl_params = collect_univ_params(inductive_decl_type(d), all_lvl_params);
            for (auto const & ir : inductive_decl_intros(d)) {
                all_lvl_params = collect_univ_params(intro_rule_type(ir), all_lvl_params);
            }
        }
        buffer<name> section_lvls;
        all_lvl_params.for_each([&](name const & l) {
                if (std::find(m_levels.begin(), m_levels.end(), l) == m_levels.end())
                    section_lvls.push_back(l);
            });
        std::sort(section_lvls.begin(), section_lvls.end(), [&](name const & n1, name const & n2) {
                return m_p.get_local_level_index(n1) < m_p.get_local_level_index(n2);
            });
        buffer<name> new_levels;
        new_levels.append(section_lvls);
        new_levels.append(m_levels);
        m_levels.clear();
        m_levels.append(new_levels);
    }

    /** \brief Collect section local parameters used in the inductive decls */
    void collect_section_locals(buffer<inductive_decl> const & decls, expr_struct_set & ls) {
        for (auto const & d : decls) {
            collect_locals(inductive_decl_type(d), ls);
            for (auto const & ir : inductive_decl_intros(d))
                collect_locals(intro_rule_type(ir), ls);
        }
    }

    /** \brief Make sure that every occurrence of an inductive datatype (in decls) in \c type has
        section parameters \c section_params as arguments.
    */
    expr fix_inductive_occs(expr const & type, buffer<inductive_decl> const & decls, buffer<expr> const & section_params) {
        return replace(type, [&](expr const & e) {
                if (!is_constant(e))
                    return none_expr();
                if (!std::any_of(decls.begin(), decls.end(),
                                 [&](inductive_decl const & d) { return const_name(e) == inductive_decl_name(d); }))
                    return none_expr();
                // found target
                expr r = mk_app(mk_explicit(e), section_params);
                return some_expr(r);
            });
    }

    /** \brief Include the used section parameters as additional arguments.
        The section parameters are stored in section_params
    */
    void abstract_section_locals(buffer<inductive_decl> & decls, buffer<expr> & section_params) {
        if (!in_section(m_env))
            return;
        expr_struct_set section_locals;
        collect_section_locals(decls, section_locals);
        if (section_locals.empty())
            return;
        sort_section_params(section_locals, m_p, section_params);
        // First, add section_params to inductive types type.
        for (inductive_decl & d : decls) {
            d = update_inductive_decl(d, Pi(section_params, inductive_decl_type(d), m_p));
        }
        // Add section_params to introduction rules type, and also "fix"
        // occurrences of inductive types.
        for (inductive_decl & d : decls) {
            buffer<intro_rule> new_irs;
            for (auto const & ir : inductive_decl_intros(d)) {
                expr type = intro_rule_type(ir);
                type = fix_inductive_occs(type, decls, section_params);
                type = Pi_as_is(section_params, type, m_p);
                bool strict = m_relaxed_implicit_infer.contains(intro_rule_name(ir));
                type = infer_implicit(type, section_params.size(), strict);
                new_irs.push_back(update_intro_rule(ir, type));
            }
            d = update_inductive_decl(d, new_irs);
        }
    }

    /** \brief Declare inductive types in the scratch environment as var_decls.
        We use this trick to be able to elaborate the introduction rules.
    */
    void declare_inductive_types(buffer<inductive_decl> & decls) {
        level_param_names ls = to_list(m_levels.begin(), m_levels.end());
        for (auto const & d : decls) {
            name d_name; expr d_type;
            std::tie(d_name, d_type, std::ignore) = d;
            m_env = m_env.add(check(m_env, mk_var_decl(d_name, ls, d_type)));
        }
        m_tc = mk_type_checker_with_hints(m_env, m_p.mk_ngen(), false);
    }

    /** \brief Traverse the introduction rule type and collect the universes where non-parameters reside in \c r_lvls.
        This information is used to compute the resultant universe level for the inductive datatype declaration.
     */
    void accumulate_levels(expr intro_type, buffer<level> & r_lvls) {
        unsigned i = 0;
        while (is_pi(intro_type)) {
            if (i >= m_num_params) {
                expr s  = m_tc->ensure_type(binding_domain(intro_type)).first;
                level l = sort_level(s);
                if (l == m_u) {
                    // ignore, this is the auxiliary level
                } else if (occurs(m_u, l)) {
                    throw exception("failed to infer inductive datatype resultant universe, provide the universe levels explicitly");
                } else if (std::find(r_lvls.begin(), r_lvls.end(), l) == r_lvls.end()) {
                    r_lvls.push_back(l);
                }
            }
            intro_type = instantiate(binding_body(intro_type), mk_local_for(intro_type));
            i++;
        }
    }

    /** \brief Elaborate introduction rules and destructively update \c decls with the elaborated versions.
        \remark This method is invoked only after all inductive datatype types have been elaborated and
        inserted into the scratch environment m_env.

        This method also store in r_lvls inferred levels that must be in the resultant universe.
    */
    void elaborate_intro_rules(buffer<inductive_decl> & decls, buffer<level> & r_lvls) {
        for (auto & d : decls) {
            name d_name; expr d_type; list<intro_rule> d_intros;
            std::tie(d_name, d_type, d_intros) = d;
            buffer<intro_rule> new_irs;
            for (auto const & ir : d_intros) {
                name ir_name; expr ir_type;
                std::tie(ir_name, ir_type) = ir;
                level_param_names new_ls;
                std::tie(ir_type, new_ls) = m_p.elaborate_at(m_env, ir_type);
                for (auto l : new_ls) m_levels.push_back(l);
                accumulate_levels(ir_type, r_lvls);
                new_irs.push_back(intro_rule(ir_name, ir_type));
            }
            d = inductive_decl(d_name, d_type, to_list(new_irs.begin(), new_irs.end()));
        }
    }

    /** \brief If old_num_univ_params < m_levels.size(), then new universe params were collected when elaborating
        the introduction rules. This method include them in all occurrences of the inductive datatype decls.
    */
    void include_extra_univ_levels(buffer<inductive_decl> & decls, unsigned old_num_univ_params) {
        if (m_levels.size() == old_num_univ_params)
            return;
        buffer<level> tmp;
        for (auto l : m_levels) tmp.push_back(mk_param_univ(l));
        levels new_ls = to_list(tmp.begin(), tmp.end());
        for (auto & d : decls) {
            buffer<intro_rule> new_irs;
            for (auto & ir : inductive_decl_intros(d)) {
                expr new_type = replace(intro_rule_type(ir), [&](expr const & e) {
                        if (!is_constant(e))
                            return none_expr();
                        if (!std::any_of(decls.begin(), decls.end(),
                                         [&](inductive_decl const & d) { return const_name(e) == inductive_decl_name(d); }))
                            return none_expr();
                        // found target
                        expr r = update_constant(e, new_ls);
                        return some_expr(r);
                    });
                new_irs.push_back(update_intro_rule(ir, new_type));
            }
            d = update_inductive_decl(d, new_irs);
        }
    }

    /** \brief Update the resultant universe level of the inductive datatypes using the inferred universe \c r_lvl */
    void update_resultant_universe(buffer<inductive_decl> & decls, level const & r_lvl) {
        for (inductive_decl & d : decls) {
            expr t = inductive_decl_type(d);
            t = update_result_sort(t, r_lvl);
            d = update_inductive_decl(d, t);
        }
    }

    /** \brief Create an alias for the fully qualified name \c full_id. */
    environment create_alias(environment env, name const & full_id, levels const & section_leves, buffer<expr> const & section_params) {
        name id(full_id.get_string());
        if (in_section(env)) {
            expr r = mk_explicit(mk_constant(full_id, section_leves));
            r = mk_app(r, section_params);
            m_p.add_local_expr(id, r);
        }
        if (full_id != id)
            env = add_expr_alias_rec(env, id, full_id);
        return env;
    }

    /** \brief Add aliases for the inductive datatype, introduction and elimination rules */
    environment add_aliases(environment env, level_param_names const & ls, buffer<expr> const & section_params,
                            buffer<inductive_decl> const & decls) {
        // Create aliases/local refs
        levels section_levels = collect_section_levels(ls, m_p);
        for (auto & d : decls) {
            name d_name = inductive_decl_name(d);
            name d_short_name(d_name.get_string());
            env = create_alias(env, d_name, section_levels, section_params);
            env = create_alias(env, mk_rec_name(d_name), section_levels, section_params);
            for (intro_rule const & ir : inductive_decl_intros(d)) {
                name ir_name = intro_rule_name(ir);
                env = create_alias(env, ir_name, section_levels, section_params);
            }
        }
        return env;
    }

    /** \brief Auxiliary method used for debugging */
    void display(std::ostream & out, buffer<inductive_decl> const & decls) {
        if (!m_levels.empty()) {
            out << "inductive level params:";
            for (auto l : m_levels) out << " " << l;
            out << "\n";
        }
        for (auto const & d : decls) {
            name d_name; expr d_type; list<intro_rule> d_irules;
            std::tie(d_name, d_type, d_irules) = d;
            out << "inductive " << d_name << " : " << d_type << "\n";
            for (auto const & ir : d_irules) {
                name ir_name; expr ir_type;
                std::tie(ir_name, ir_type) = ir;
                out << "  | " << ir_name << " : " << ir_type << "\n";
            }
        }
        out << "\n";
    }

    environment operator()() {
        parser::no_undef_id_error_scope err_scope(m_p);
        buffer<inductive_decl> decls;
        parse_inductive_decls(decls);
        include_section_levels(decls);
        buffer<expr> section_params;
        abstract_section_locals(decls, section_params);
        m_num_params += section_params.size();
        declare_inductive_types(decls);
        unsigned num_univ_params = m_levels.size();
        buffer<level> r_lvls;
        elaborate_intro_rules(decls, r_lvls);
        include_extra_univ_levels(decls, num_univ_params);
        if (m_infer_result_universe) {
            level r_lvl = mk_result_level(m_env, r_lvls);
            update_resultant_universe(decls, r_lvl);
        }
        level_param_names ls = to_list(m_levels.begin(), m_levels.end());
        environment env = module::add_inductive(m_p.env(), ls, m_num_params, to_list(decls.begin(), decls.end()));
        return add_aliases(env, ls, section_params, decls);
    }
};

environment inductive_cmd(parser & p) {
    return inductive_cmd_fn(p)();
}

void register_inductive_cmd(cmd_table & r) {
    add_cmd(r, cmd_info("inductive",   "declare an inductive datatype", inductive_cmd));
}
}
