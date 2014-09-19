/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <utility>
#include <vector>
#include <algorithm>
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/replace_fn.h"
#include "kernel/record/record.h"
#include "library/scoped_ext.h"
#include "library/placeholder.h"
#include "library/locals.h"
#include "library/reducible.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/decl_cmds.h"

namespace lean {
static name g_assign(":=");
static name g_colon(":");
static name g_dcolon("::");
static name g_comma(",");
static name g_lparen("(");
static name g_rparen(")");
static name g_arrow("->");
static name g_extends("extends");
static name g_renaming("renaming");

static name g_tmp_prefix = name::mk_internal_unique_name();

struct structure_cmd_fn {
    typedef std::unique_ptr<type_checker> type_checker_ptr;
    typedef std::vector<pair<name, name>> rename_vector;
    parser &                   m_p;
    environment                m_env;
    name_generator             m_ngen;
    name                       m_namespace;
    name                       m_name;
    buffer<name>               m_level_names;
    name                       m_mk;
    buffer<name>               m_univ_params;
    buffer<expr>               m_params;
    expr                       m_type;
    buffer<expr>               m_parents;
    buffer<expr>               m_fields;
    buffer<notation_entry>     m_nentries;
    std::vector<rename_vector> m_renames;
    level                      m_u; // temporary auxiliary global universe used for inferring the result universe
    bool                       m_infer_result_universe;
    bool                       m_using_explicit_levels;

    structure_cmd_fn(parser & p):m_p(p), m_env(p.env()), m_ngen(p.mk_ngen()), m_namespace(get_namespace(m_env)) {
        name u_name(g_tmp_prefix, "u");
        m_env = m_env.add_universe(u_name);
        m_u = mk_global_univ(u_name);
        m_infer_result_universe = false;
        m_using_explicit_levels = false;
    }

    void parse_decl_name() {
        m_name = m_p.check_atomic_id_next("invalid 'structure', identifier expected");
        m_name = m_namespace + m_name;
        buffer<name> ls_buffer;
        if (parse_univ_params(m_p, ls_buffer)) {
            m_infer_result_universe = false;
            m_level_names.append(ls_buffer);
        } else {
            m_infer_result_universe = true;
        }
    }

    void parse_params() {
        if (!m_p.curr_is_token(g_extends) && !m_p.curr_is_token(g_assign))
            m_p.parse_binders(m_params);
        for (expr const & l : m_params)
            m_p.add_local(l);
    }

    void parse_extends() {
        if (m_p.curr_is_token(g_extends)) {
            m_p.next();
            while (true) {
                m_parents.push_back(m_p.parse_expr());
                m_renames.push_back(rename_vector());
                if (m_p.curr_is_token(g_renaming)) {
                    m_p.next();
                    rename_vector & v = m_renames.back();
                    while (!m_p.curr_is_token(g_comma)) {
                        name from = m_p.check_id_next("invalid 'renaming', identifier expected");
                        m_p.check_token_next(g_arrow, "invalid 'renaming', '->' expected");
                        name to   = m_p.check_id_next("invalid 'renaming', identifier expected");
                        v.emplace_back(from, to);
                    }
                }
                if (!m_p.curr_is_token(g_comma))
                    break;
                m_p.next();
            }
        }
    }

    void parse_result_type() {
        auto pos = m_p.pos();
        if (m_p.curr_is_token(g_colon)) {
            m_p.next();
            m_type = m_p.parse_expr();
            if (!is_sort(m_type))
                throw parser_error("invalid 'structure', 'Type' expected", pos);
        } else {
            m_type = m_p.save_pos(mk_sort(mk_level_placeholder()), pos);
        }
    }

    /** \brief Include in m_level_names any section level referenced m_type and m_fields */
    void include_section_levels() {
        if (!in_section_or_context(m_env))
            return;
        name_set all_lvl_params;
        all_lvl_params = collect_univ_params(m_type);
        for (expr const & f : m_fields)
            all_lvl_params = collect_univ_params(mlocal_type(f), all_lvl_params);
        buffer<name> section_lvls;
        all_lvl_params.for_each([&](name const & l) {
                if (std::find(m_level_names.begin(), m_level_names.end(), l) == m_level_names.end())
                    section_lvls.push_back(l);
            });
        std::sort(section_lvls.begin(), section_lvls.end(), [&](name const & n1, name const & n2) {
                return m_p.get_local_level_index(n1) < m_p.get_local_level_index(n2);
            });
        buffer<name> new_levels;
        new_levels.append(section_lvls);
        new_levels.append(m_level_names);
        m_level_names.clear();
        m_level_names.append(new_levels);
    }

    /** \brief Collect section local parameters used in m_params and m_fields */
    void collect_section_locals(expr_struct_set & ls) {
        collect_locals(m_type, ls);
        expr tmp = Pi(m_fields, Prop, m_p); // temp expr just for collecting section parameters occurring in the fields.
        collect_locals(tmp, ls);
    }

    /** \brief Include the used section parameters as additional arguments.
        The section parameters are stored in section_params
    */
    void abstract_section_locals(buffer<expr> & section_params) {
        if (!in_section_or_context(m_env))
            return;
        expr_struct_set section_locals;
        collect_section_locals(section_locals);
        if (section_locals.empty())
            return;
        sort_section_params(section_locals, m_p, section_params);
        m_type = Pi_as_is(section_params, m_type, m_p);
    }

    /** \brief Return the universe level of the given type, if it is not a sort, then raise an exception. */
    level get_result_sort(expr d_type) {
        while (is_pi(d_type))
            d_type = binding_body(d_type);
        lean_assert(is_sort(d_type));
        return sort_level(d_type);
    }

    /** \brief Update the result sort of the given type */
    expr update_result_sort(expr t, level const & l) {
        if (is_pi(t)) {
            return update_binding(t, binding_domain(t), update_result_sort(binding_body(t), l));
        } else if (is_sort(t)) {
            return update_sort(t, l);
        } else {
            lean_unreachable();
        }
    }

    void elaborate_type() {
        level l = get_result_sort(m_type);
        if (is_placeholder(l)) {
            if (m_using_explicit_levels)
                throw parser_error("resultant universe must be provided, when using explicit universe levels", m_p.pos());
            m_type = update_result_sort(m_type, m_u);
            m_infer_result_universe = true;
        }
        level_param_names ls;
        std::tie(m_type, ls) = m_p.elaborate_at(m_env, m_type);
        to_buffer(ls, m_level_names);
    }

    void add_tmp_record_decl() {
        m_env = m_env.add(check(m_env, mk_var_decl(m_name, to_list(m_level_names.begin(), m_level_names.end()), m_type)));
    }

    levels to_levels(buffer<name> const & lvl_names) {
        buffer<level> ls;
        for (name const & n : lvl_names) ls.push_back(mk_param_univ(n));
        return to_list(ls.begin(), ls.end());
    }

    expr elaborate_intro(buffer<expr> & params) {
        expr t = m_type;
        while (is_pi(t)) {
            expr p = mk_local(binding_name(t), binding_domain(t), binding_info(t));
            t = instantiate(binding_body(t), p);
            params.push_back(p);
        }
        levels lvls = to_levels(m_level_names);
        expr intro_type = mk_app(mk_constant(m_name, lvls), params);
        intro_type = Pi(m_fields, intro_type, m_p);
        intro_type = Pi_as_is(params, intro_type, m_p);
        level_param_names new_ls;
        std::tie(intro_type, new_ls) = m_p.elaborate_at(m_env, intro_type);
        for (name const & l : new_ls)
            m_level_names.push_back(l);
        if (!empty(new_ls)) {
            // replace mk_constant(m_name, lvls) with mk_constant(m_name, new_lvls)
            levels new_lvls = to_levels(m_level_names);
            intro_type = replace(intro_type, [&](expr const & e) {
                    if (is_constant(e) && const_name(e) == m_name) {
                        return some_expr(mk_constant(m_name, new_lvls));
                    } else {
                        return none_expr();
                    }
                });
        }
        return intro_type;
    }

    /** \brief Traverse the introduction rule type and collect the universes where non-parameters reside in \c r_lvls.
        This information is used to compute the resultant universe level for the inductive datatype declaration.
     */
    void accumulate_levels(expr intro_type, unsigned num_params, buffer<level> & r_lvls) {
        auto tc = mk_type_checker(m_env, m_p.mk_ngen(), false);
        unsigned i = 0;
        while (is_pi(intro_type)) {
            if (i >= num_params) {
                expr s  = tc->ensure_type(binding_domain(intro_type)).first;
                level l = sort_level(s);
                if (l == m_u) {
                    // ignore, this is the auxiliary level
                } else if (occurs(m_u, l)) {
                    throw exception("failed to infer record resultant universe, provide the universe levels explicitly");
                } else if (std::find(r_lvls.begin(), r_lvls.end(), l) == r_lvls.end()) {
                    r_lvls.push_back(l);
                }
            }
            intro_type = instantiate(binding_body(intro_type),
                                     mk_local(m_p.mk_fresh_name(), binding_name(intro_type), binding_domain(intro_type), binding_info(intro_type)));
            i++;
        }
    }

    environment operator()() {
        parser::local_scope scope(m_p);
        parse_decl_name();
        parse_params();
        parse_extends();
        // TODO(Leo): process extends
        parse_result_type();
        m_p.check_token_next(g_assign, "invalid 'structure', ':=' expected");
        m_mk = m_p.check_atomic_id_next("invalid 'structure', identifier expected");
        m_p.check_token_next(g_dcolon, "invalid 'structure', '::' expected");
        m_p.parse_binders(m_fields, m_nentries);
        m_type = Pi(m_params, m_type, m_p);
        include_section_levels();
        buffer<expr> section_params;
        abstract_section_locals(section_params);
        elaborate_type();
        add_tmp_record_decl();
        buffer<expr> all_params;
        expr intro_type = elaborate_intro(all_params);
        if (m_infer_result_universe) {
            buffer<level> r_lvls;
            unsigned num_params = all_params.size();
            accumulate_levels(intro_type, num_params, r_lvls);
            level r_lvl = mk_result_level(m_env, r_lvls);
            m_type = update_result_sort(m_type, r_lvl);
        }
        m_env = record::add_record(m_p.env(), to_list(m_level_names.begin(), m_level_names.end()), m_name, m_type,
                                   m_mk, intro_type);
        // TODO(Leo): create aliases, declare notation, create to_parent methods.
        return m_env;
    }
};

environment structure_cmd(parser & p) {
    return structure_cmd_fn(p)();
}

void register_structure_cmd(cmd_table & r) {
    add_cmd(r, cmd_info("structure",   "declare a new structure/record type", structure_cmd));
}
}
