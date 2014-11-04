/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <utility>
#include <vector>
#include <algorithm>
#include "util/sstream.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "kernel/error_msgs.h"
#include "kernel/inductive/inductive.h"
#include "library/scoped_ext.h"
#include "library/placeholder.h"
#include "library/locals.h"
#include "library/reducible.h"
#include "library/unifier.h"
#include "library/module.h"
#include "library/aliases.h"
#include "library/explicit.h"
#include "library/protected.h"
#include "library/definitional/rec_on.h"
#include "library/definitional/induction_on.h"
#include "library/definitional/cases_on.h"
#include "library/definitional/unit.h"
#include "library/definitional/projection.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/elaborator_exception.h"
#include "frontends/lean/type_util.h"

namespace lean {
static name * g_tmp_prefix = nullptr;

void initialize_structure_cmd() {
    g_tmp_prefix = new name(name::mk_internal_unique_name());
}

void finalize_structure_cmd() {
    delete g_tmp_prefix;
}

struct structure_cmd_fn {
    typedef std::unique_ptr<type_checker> type_checker_ptr;
    typedef std::vector<pair<name, name>> rename_vector;
    // field_map[i] contains the position of the \c i-th field of a parent structure into this one.
    typedef std::vector<unsigned>         field_map;
    typedef type_modifiers                modifiers;

    parser &                   m_p;
    environment                m_env;
    name_generator             m_ngen;
    type_checker_ptr           m_tc;
    name                       m_namespace;
    name                       m_name;
    pos_info                   m_name_pos;
    buffer<name>               m_level_names;
    modifiers                  m_modifiers;
    buffer<expr>               m_params;
    expr                       m_type;
    buffer<expr>               m_parents;
    name                       m_mk;
    pos_info                   m_mk_pos;
    implicit_infer_kind        m_mk_infer;
    buffer<expr>               m_fields;
    std::vector<rename_vector> m_renames;
    std::vector<field_map>     m_field_maps;
    bool                       m_infer_result_universe;
    bool                       m_using_explicit_levels;
    levels                     m_ctx_levels; // context levels for creating aliases
    buffer<expr>               m_ctx_locals; // context local constants for creating aliases

    structure_cmd_fn(parser & p):m_p(p), m_env(p.env()), m_ngen(p.mk_ngen()), m_namespace(get_namespace(m_env)) {
        m_tc = mk_type_checker(m_env, m_p.mk_ngen(), false);
        m_infer_result_universe = false;
        m_using_explicit_levels = false;
    }

    /** \brief Parse structure name and (optional) universe parameters */
    void parse_decl_name() {
        m_name_pos = m_p.pos();
        m_name = m_p.check_atomic_id_next("invalid 'structure', identifier expected");
        m_name = m_namespace + m_name;
        buffer<name> ls_buffer;
        if (parse_univ_params(m_p, ls_buffer)) {
            m_infer_result_universe = false;
            m_level_names.append(ls_buffer);
        } else {
            m_infer_result_universe = true;
        }
        m_modifiers.parse(m_p);
    }

    /** \brief Parse structure parameters */
    void parse_params() {
        if (!m_p.curr_is_token(get_extends_tk()) && !m_p.curr_is_token(get_assign_tk()))
            m_p.parse_binders(m_params);
        for (expr const & l : m_params)
            m_p.add_local(l);
    }

    /** \brief Check whether \c parent is really an inductive datatype declaration that can be viewed as a "record".
        That is, it is not part of a mutually recursive declaration, it has only one constructor,
        and it does not have indicies.
    */
    void check_parent(expr const & parent, pos_info const & pos) {
        expr const & fn = get_app_fn(parent);
        if (!is_constant(fn))
            throw parser_error("invalid 'structure', expression must be a 'parent' structure", pos);
        name const & S = const_name(fn);
        optional<inductive::inductive_decls> idecls = inductive::is_inductive_decl(m_env, S);
        if (!idecls || length(std::get<2>(*idecls)) != 1)
            throw parser_error(sstream() << "invalid 'structure' extends, '" << S << "' is not a structure", pos);
        inductive::inductive_decl decl   = head(std::get<2>(*idecls));
        if (length(inductive::inductive_decl_intros(decl)) != 1 || *inductive::get_num_indices(m_env, S) != 0)
            throw parser_error(sstream() << "invalid 'structure' extends, '" << S << "' is not a structure", pos);
    }

    /** \brief Return the universe parameters, number of parameters and introduction rule for the given parent structure */
    std::tuple<level_param_names, unsigned, inductive::intro_rule> get_parent_info(name const & parent) {
        inductive::inductive_decls idecls = *inductive::is_inductive_decl(m_env, parent);
        inductive::intro_rule intro = head(inductive::inductive_decl_intros(head(std::get<2>(idecls))));
        return std::make_tuple(std::get<0>(idecls), std::get<1>(idecls), intro);
    }

    /** \brief Sign an error if the constructor \c intro_type does not have a field named \c from_id */
    void check_from_rename(name const & parent_name, expr intro_type, name const & from_id, pos_info const & from_pos) {
        while (is_pi(intro_type)) {
            if (binding_name(intro_type) == from_id)
                return;
            intro_type = binding_body(intro_type);
        }
        throw parser_error(sstream() << "invalid 'structure' renaming, parent structure '" << parent_name  << "' "
                           << "does not contain field '" << from_id << "'", from_pos);
    }

    /** \brief Parse optional extends clause */
    void parse_extends() {
        if (m_p.curr_is_token(get_extends_tk())) {
            m_p.next();
            while (true) {
                auto pos = m_p.pos();
                expr parent = m_p.parse_expr();
                m_parents.push_back(parent);
                check_parent(parent, pos);
                name const & parent_name = const_name(get_app_fn(parent));
                auto parent_info         = get_parent_info(parent_name);
                unsigned nparams         = std::get<1>(parent_info);
                inductive::intro_rule intro = std::get<2>(parent_info);
                expr intro_type = inductive::intro_rule_type(intro);
                for (unsigned i = 0; i < nparams; i++) {
                    if (!is_pi(intro_type))
                        throw parser_error("invalid 'structure' extends, parent structure seems to be ill-formed", pos);
                    intro_type = binding_body(intro_type);
                }
                m_renames.push_back(rename_vector());
                if (m_p.curr_is_token(get_renaming_tk())) {
                    m_p.next();
                    rename_vector & v = m_renames.back();
                    while (m_p.curr_is_identifier()) {
                        auto from_pos = m_p.pos();
                        name from_id  = m_p.get_name_val();
                        if (std::find_if(v.begin(), v.end(),
                                         [&](pair<name, name> const & p) { return p.first == from_id; }) != v.end())
                            throw parser_error(sstream() << "invalid 'structure' renaming, a rename from '" <<
                                               from_id << "' has already been defined", from_pos);
                        check_from_rename(parent_name, intro_type, from_id, from_pos);
                        m_p.next();
                        m_p.check_token_next(get_arrow_tk(), "invalid 'structure' renaming, '->' expected");
                        name to_id = m_p.check_id_next("invalid 'structure' renaming, identifier expected");
                        if (from_id == to_id)
                            throw parser_error(sstream() << "invalid 'structure' renaming, redundant rename", from_pos);
                        v.emplace_back(from_id, to_id);
                    }
                }
                if (!m_p.curr_is_token(get_comma_tk()))
                    break;
                m_p.next();
            }
        }
    }

    /** \brief Parse resultant universe */
    void parse_result_type() {
        auto pos = m_p.pos();
        if (m_p.curr_is_token(get_colon_tk())) {
            m_p.next();
            m_type = m_p.parse_expr();
            if (!is_sort(m_type))
                throw parser_error("invalid 'structure', 'Type' expected", pos);
        } else {
            m_type = m_p.save_pos(mk_sort(mk_level_placeholder()), pos);
        }
    }

    /** \brief Parse parameters, extends clauses and resultant type */
    void parse_header() {
        parser::local_scope scope(m_p);
        parse_decl_name();
        parse_params();
        parse_extends();
        parse_result_type();
    }

    /** \brief Update the local constants in \c locals using the content of the Pi expression \c new_tmp.
        This method assumes that new_tmp contains at least locals.size() nested Pi's.
    */
    expr update_locals(expr new_tmp, buffer<expr> & locals) {
        for (unsigned i = 0; i < locals.size(); i++) {
            expr new_local = mk_local(binding_name(new_tmp), binding_domain(new_tmp), binding_info(new_tmp));
            locals[i]      = new_local;
            new_tmp        = instantiate(binding_body(new_tmp), new_local);
        }
        return new_tmp;
    }

    expr update_parents(expr new_tmp) {
        for (unsigned i = 0; i < m_parents.size(); i++) {
            m_parents[i]   = copy_tag(m_parents[i], expr(binding_domain(new_tmp)));
            new_tmp        = binding_body(new_tmp);
            lean_assert(closed(new_tmp));
        }
        return new_tmp;
    }

    /** \brief elaborate parameters and "parent" types */
    void elaborate_header() {
        buffer<expr> include_vars;
        m_p.get_include_variables(include_vars);
        buffer<expr> tmp_locals;
        tmp_locals.append(m_params);
        for (expr const & parent : m_parents)
            tmp_locals.push_back(mk_local(m_ngen.next(), parent));
        expr tmp       = Pi_as_is(include_vars, Pi(tmp_locals, m_type, m_p), m_p);
        list<expr> ctx = m_p.locals_to_context();
        level_param_names new_ls;
        expr new_tmp;
        std::tie(new_tmp, new_ls) = m_p.elaborate_type(tmp, ctx);
        levels new_meta_ls = map2<level>(new_ls, [](name const & n) { return mk_meta_univ(n); });
        new_tmp = instantiate_univ_params(new_tmp, new_ls, new_meta_ls);
        new_tmp = update_locals(new_tmp, include_vars);
        new_tmp = update_locals(new_tmp, m_params);
        buffer<expr> explicit_params;
        explicit_params.append(m_params);
        m_params.clear();
        m_params.append(include_vars);
        m_params.append(explicit_params);
        new_tmp = update_parents(new_tmp);
        m_type = new_tmp;
    }

    void throw_ill_formed_parent(name const & parent_name) {
        throw exception(sstream() << "invalid 'structure' header, parent structure '" << parent_name << "' is ill-formed");
    }

    /** \brief Check if \c fname has been renamed, and return new name */
    name rename(rename_vector const & v, name const & fname) {
        for (auto const & p : v) {
            if (p.first == fname)
                return p.second;
        }
        return fname;
    }

    /** \brief If \c fname matches the name of an existing field, then check if
        the types are definitionally equal (store any generated unification constraints in cseq),
        and return the index of the existing field. */
    optional<unsigned> merge(expr const & parent, name const & fname, expr const & ftype, constraint_seq & cseq) {
        for (unsigned i = 0; i < m_fields.size(); i++) {
            if (local_pp_name(m_fields[i]) == fname) {
                if (m_tc->is_def_eq(mlocal_type(m_fields[i]), ftype, justification(), cseq)) {
                    return optional<unsigned>(i);
                } else {
                    expr prev_ftype = mlocal_type(m_fields[i]);
                    throw_elaborator_exception(m_env, parent, [=](formatter const & fmt) {
                            format r = format("invalid 'structure' header, field '");
                            r += format(fname);
                            r += format("' from '");
                            r += format(const_name(get_app_fn(parent)));
                            r += format("' has already been declared with a different type");
                            r += pp_indent_expr(fmt, prev_ftype);
                            r += compose(line(), format("and"));
                            r += pp_indent_expr(fmt, ftype);
                            return r;
                        });
                }
            }
        }
        return optional<unsigned>();
    }

    /** \brief Process extends clauses.
        Return unification constraints when processing fields of parent structures.
        The constraints are generated when "merging" the fields from different parents.

        This method also populates the vector m_field_maps and m_fields.
    */
    constraint_seq process_extends() {
        lean_assert(m_fields.empty());
        lean_assert(m_field_maps.empty());
        constraint_seq cseq;
        for (unsigned i = 0; i < m_parents.size(); i++) {
            expr const & parent = m_parents[i];
            rename_vector const & renames = m_renames[i];
            m_field_maps.push_back(field_map());
            field_map & fmap = m_field_maps.back();
            buffer<expr> args;
            expr const & parent_fn = get_app_args(parent, args);
            level_param_names lparams; unsigned nparams; inductive::intro_rule intro;
            name const & parent_name = const_name(parent_fn);
            std::tie(lparams, nparams, intro) = get_parent_info(parent_name);
            expr intro_type = inductive::intro_rule_type(intro);
            intro_type      = instantiate_univ_params(intro_type, lparams, const_levels(parent_fn));
            if (nparams != args.size()) {
                throw_elaborator_exception(m_env,
                                           sstream() << "invalid 'structure' header, number of argument "
                                           "mismatch for parent structure '" << parent_name << "'",
                                           parent);
            }
            for (expr const & arg : args) {
                if (!is_pi(intro_type))
                    throw_ill_formed_parent(parent_name);
                intro_type = instantiate(binding_body(intro_type), arg);
            }
            while (is_pi(intro_type)) {
                name fname = binding_name(intro_type);
                fname      = rename(renames, fname);
                expr const & ftype = binding_domain(intro_type);
                expr field;
                if (auto fidx = merge(parent, fname, ftype, cseq)) {
                    fmap.push_back(*fidx);
                    field = m_fields[*fidx];
                    if (local_info(field) != binding_info(intro_type)) {
                        throw_elaborator_exception(m_env,
                                                   sstream() << "invalid 'structure' header, field '" << fname <<
                                                   "' has already been declared with a different binder annotation",
                                                   parent);
                    }
                } else {
                    field = mk_local(fname, ftype, binding_info(intro_type));
                    fmap.push_back(m_fields.size());
                    m_fields.push_back(field);
                }
                intro_type = instantiate(binding_body(intro_type), field);
            }
        }
        lean_assert(m_parents.size() == m_field_maps.size());
        return cseq;
    }

    void solve_constraints(constraint_seq const & cseq) {
        if (!cseq)
            return;
        buffer<constraint> cs;
        cseq.linearize(cs);
        bool use_exceptions = true;
        bool discard        = true;
        unifier_config cfg(use_exceptions, discard);
        unify_result_seq rseq = unify(m_env, cs.size(), cs.data(), m_ngen.mk_child(), substitution(), cfg);
        auto p = rseq.pull();
        lean_assert(p);
        substitution subst = p->first.first;
        for (expr & parent : m_parents)
            parent = subst.instantiate(parent);
        for (expr & param : m_params)
            param = subst.instantiate(param);
        for (expr & field : m_fields)
            field = subst.instantiate(field);
    }

    /** \brief Parse header, elaborate it, and process parents (aka extends clauses) */
    void process_header() {
        parse_header();
        elaborate_header();
        constraint_seq cseq = process_extends();
        solve_constraints(cseq);
    }

    /** \brief Add params and fields to parser local scope */
    void add_locals() {
        for (expr const & param : m_params)
            m_p.add_local(param);
        for (expr const & field : m_fields)
            m_p.add_local(field);
    }

    /** \brief Check if new field names collide with fields inherited from parent datastructures */
    void check_new_field_names(buffer<expr> const & new_fields) {
        for (expr const & new_field : new_fields) {
            if (std::find_if(m_fields.begin(), m_fields.end(),
                             [&](expr const & inherited_field) {
                                 return local_pp_name(inherited_field) == local_pp_name(new_field);
                             }) != m_fields.end()) {
                throw_elaborator_exception(m_env, sstream() << "field '" << local_pp_name(new_field) <<
                                           "' has been declared in parent structure",
                                           new_field);
            }
        }
    }

    /** \brief Parse new fields declared in this structure */
    void parse_new_fields(buffer<expr> & new_fields) {
        parser::local_scope scope(m_p);
        add_locals();
        m_p.parse_binders(new_fields);
        check_new_field_names(new_fields);
    }


    /** \brief Elaborate new fields, and copy them to m_fields */
    void elaborate_new_fields(buffer<expr> & new_fields) {
        list<expr> ctx = m_p.locals_to_context();
        expr dummy = mk_Prop();
        unsigned j = m_parents.size();
        while (j > 0) {
            --j;
            dummy = mk_arrow(mk_as_is(m_parents[j]), dummy);
        }
        expr tmp = Pi_as_is(m_params, Pi_as_is(m_fields, Pi(new_fields, dummy, m_p), m_p), m_p);
        level_param_names new_ls;
        expr new_tmp;
        std::tie(new_tmp, new_ls) = m_p.elaborate_type(tmp, ctx);
        for (auto new_l : new_ls)
            m_level_names.push_back(new_l);
        new_tmp = update_locals(new_tmp, m_params);
        new_tmp = update_locals(new_tmp, m_fields);
        new_tmp = update_locals(new_tmp, new_fields);
        new_tmp = update_parents(new_tmp);
        lean_assert(new_tmp == mk_Prop());
        m_fields.append(new_fields);
    }

    /** \brief Parse new fields declared by this structure, and elaborate them. */
    void process_new_fields() {
        buffer<expr> new_fields;
        parse_new_fields(new_fields);
        elaborate_new_fields(new_fields);
    }

    /** \brief Traverse fields and collect the universes they reside in \c r_lvls.
        This information is used to compute the resultant universe level for the inductive datatype declaration.
    */
    void accumulate_levels(buffer<level> & r_lvls) {
        for (expr const & field : m_fields) {
            expr s  = m_tc->ensure_type(mlocal_type(field)).first;
            level l = sort_level(s);
            if (std::find(r_lvls.begin(), r_lvls.end(), l) == r_lvls.end()) {
                r_lvls.push_back(l);
            }
        }
    }

    /** \brief Compute resultant universe (if it was not provided explicitly) based on the universes
        where the fields "reside" */
    void infer_resultant_universe() {
        if (m_infer_result_universe) {
            buffer<level> r_lvls;
            accumulate_levels(r_lvls);
            level r_lvl = mk_result_level(m_env, r_lvls);
            m_type      = mk_sort(r_lvl);
        }
    }

    /** \brief Display m_fields (for debugging purposes) */
    void display_fields(std::ostream & out) {
        for (expr const & field : m_fields) {
            out << ">> " << mlocal_name(field) << " : " << mlocal_type(field) << "\n";
        }
    }

    /** \brief Collect context local constants used in the declaration. */
    void collect_ctx_locals(buffer<expr> & locals) {
        if (!m_p.has_locals())
            return;
        expr dummy = mk_Prop();
        expr tmp   = Pi(m_params, Pi(m_fields, dummy));
        expr_struct_set local_set;
        ::lean::collect_locals(tmp, local_set);
        sort_locals(local_set, m_p, locals);
    }

    /** \brief Add context locals as extra parameters */
    void add_ctx_locals(buffer<expr> const & ctx_locals) {
        buffer<expr> params;
        params.append(m_params);
        m_params.clear();
        m_params.append(ctx_locals);
        m_params.append(params);
    }

    /** \brief Include in m_level_names any local level referenced m_type and m_fields */
    void include_ctx_levels() {
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

    expr mk_structure_type() {
        return Pi(m_params, m_type);
    }

    expr mk_intro_type() {
        levels ls = param_names_to_levels(to_list(m_level_names.begin(), m_level_names.end()));
        expr r    = mk_app(mk_constant(m_name, ls), m_params);
        r         = Pi(m_params, Pi(m_fields, r));
        return infer_implicit_params(r, m_params.size(), m_mk_infer);
    }

    void save_info(name const & n, name const & k, pos_info const & pos) {
        expr type = m_env.get(n).get_type();
        m_p.add_decl_index(n, pos, k, type);
    }

    void add_alias(name const & n, bool composite = true) {
        m_env = ::lean::add_alias(m_p, m_env, composite, n, m_ctx_levels, m_ctx_locals);
    }

    void add_rec_alias(name const & n) {
        bool composite = true;
        m_env = ::lean::add_alias(m_p, m_env, composite, n, levels(mk_level_placeholder(), m_ctx_levels), m_ctx_locals);
    }

    void declare_inductive_type() {
        expr structure_type = mk_structure_type();
        expr intro_type     = mk_intro_type();

        level_param_names lnames = to_list(m_level_names.begin(), m_level_names.end());
        inductive::intro_rule intro(m_mk, intro_type);
        inductive::inductive_decl  decl(m_name, structure_type, to_list(intro));
        m_env = module::add_inductive(m_env, lnames, m_params.size(), to_list(decl));
        save_info(m_name, "structure", m_name_pos);
        name rec_name = inductive::get_elim_name(m_name);
        save_info(rec_name, "recursor", m_name_pos);
        save_info(m_mk, "intro", m_mk_pos);
        m_env = add_namespace(m_env, m_name);
        m_env = add_protected(m_env, rec_name);
        add_alias(m_name, false);
        add_alias(m_mk);
        add_rec_alias(rec_name);
    }

    void save_def_info(name const & n) {
        save_info(n, "definition", m_name_pos);
    }

    void save_proj_info(name const & n) {
        save_info(n, "projection", m_name_pos);
    }

    void declare_projections() {
        m_env = mk_projections(m_env, m_name, m_modifiers.is_class());
        for (expr const & field : m_fields) {
            name field_name = m_name + mlocal_name(field);
            save_proj_info(field_name);
            add_alias(field_name);
        }
    }

    void declare_auxiliary() {
        bool has_unit = has_unit_decls(m_env);
        m_env = mk_rec_on(m_env, m_name);
        m_env = mk_induction_on(m_env, m_name);
        name rec_on_name(m_name, "rec_on");
        name induction_on_name(m_name, "induction_on");
        add_rec_alias(rec_on_name);
        add_rec_alias(induction_on_name);
        save_def_info(rec_on_name);
        save_def_info(induction_on_name);
        if (has_unit) {
            m_env = mk_cases_on(m_env, m_name);
            name cases_on_name(m_name, "cases_on");
            save_def_info(cases_on_name);
            add_rec_alias(cases_on_name);
        }
    }

    void declare_coercions() {
        lean_assert(m_parents.size() == m_field_maps.size());
        level_param_names lnames = to_list(m_level_names.begin(), m_level_names.end());
        levels st_ls             = param_names_to_levels(lnames);
        for (unsigned i = 0; i < m_parents.size(); i++) {
            expr const & parent            = m_parents[i];
            field_map const & fmap         = m_field_maps[i];
            buffer<expr> parent_params;
            expr const & parent_fn         = get_app_args(parent, parent_params);
            levels const & parent_ls       = const_levels(parent_fn);
            name const & parent_name       = const_name(parent_fn);
            auto parent_info               = get_parent_info(parent_name);
            name const & parent_intro_name = inductive::intro_rule_name(std::get<2>(parent_info));
            expr parent_intro              = mk_app(mk_constant(parent_intro_name, parent_ls), parent_params);
            expr parent_type               = m_tc->infer(parent).first;
            if (!is_sort(parent_type))
                throw_ill_formed_parent(parent_name);
            level parent_rlvl              = sort_level(parent_type);
            expr st_type                   = mk_app(mk_constant(m_name, st_ls), m_params);
            binder_info bi;
            if (m_modifiers.is_class())
                bi = mk_inst_implicit_binder_info();
            expr st                        = mk_local(m_ngen.next(), "s", st_type, bi);
            expr coercion_type             = infer_implicit(Pi(m_params, Pi(st, parent)), m_params.size(), true);;
            levels rec_ls                  = levels(parent_rlvl, st_ls);
            expr rec                       = mk_app(mk_constant(inductive::get_elim_name(m_name), rec_ls), m_params);
            expr type_former               = Fun(st, parent);
            rec                            = mk_app(rec, type_former);
            expr minor_premise             = parent_intro;
            for (unsigned idx : fmap)
                minor_premise = mk_app(minor_premise, m_fields[idx]);
            minor_premise                  = Fun(m_fields, minor_premise);
            rec                            = mk_app(rec, minor_premise, st);
            expr coercion_value            = Fun(m_params, Fun(st, rec));
            name coercion_name             = m_name + parent_name.append_before("to_");

            bool opaque                    = false;
            declaration coercion_decl      = mk_definition(m_env, coercion_name, lnames, coercion_type, coercion_value,
                                                           opaque);
            m_env = module::add(m_env, check(m_env, coercion_decl));
            m_env = set_reducible(m_env, coercion_name, reducible_status::On);
            save_def_info(coercion_name);
            add_alias(coercion_name);
        }
    }

    environment operator()() {
        process_header();
        m_p.check_token_next(get_assign_tk(), "invalid 'structure', ':=' expected");
        m_mk_pos = m_p.pos();
        m_mk = m_p.check_atomic_id_next("invalid 'structure', identifier expected");
        m_mk = m_name + m_mk;
        m_mk_infer = parse_implicit_infer_modifier(m_p);
        m_p.check_token_next(get_dcolon_tk(), "invalid 'structure', '::' expected");
        process_new_fields();
        infer_resultant_universe();
        collect_ctx_locals(m_ctx_locals);
        add_ctx_locals(m_ctx_locals);
        include_ctx_levels();
        m_ctx_levels = collect_local_nonvar_levels(m_p, to_list(m_level_names.begin(), m_level_names.end()));
        declare_inductive_type();
        declare_projections();
        declare_auxiliary();
        declare_coercions();
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
