/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <utility>
#include <vector>
#include <algorithm>
#include <string>
#include "util/sstream.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "kernel/error_msgs.h"
#include "kernel/inductive/inductive.h"
#include "library/scoped_ext.h"
#include "library/normalize.h"
#include "library/placeholder.h"
#include "library/locals.h"
#include "library/reducible.h"
#include "library/unifier.h"
#include "library/module.h"
#include "library/aliases.h"
#include "library/coercion.h"
#include "library/explicit.h"
#include "library/protected.h"
#include "library/class.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/projection.h"
#include "library/kernel_serializer.h"
#include "library/definitional/rec_on.h"
#include "library/definitional/induction_on.h"
#include "library/definitional/cases_on.h"
#include "library/definitional/projection.h"
#include "library/definitional/no_confusion.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/elaborator_exception.h"
#include "frontends/lean/type_util.h"

#ifndef LEAN_DEFAULT_STRUCTURE_INTRO
#define LEAN_DEFAULT_STRUCTURE_INTRO "mk"
#endif

#ifndef LEAN_DEFAULT_STRUCTURE_ETA
#define LEAN_DEFAULT_STRUCTURE_ETA false
#endif

#ifndef LEAN_DEFAULT_STRUCTURE_PROJ_MK
#define LEAN_DEFAULT_STRUCTURE_PROJ_MK false
#endif

namespace lean {
static name * g_tmp_prefix  = nullptr;
static name * g_gen_eta     = nullptr;
static name * g_gen_proj_mk = nullptr;

bool get_structure_eta_thm(options const & o) { return o.get_bool(*g_gen_eta, LEAN_DEFAULT_STRUCTURE_ETA); }
bool get_structure_proj_mk_thm(options const & o) { return o.get_bool(*g_gen_proj_mk, LEAN_DEFAULT_STRUCTURE_ETA); }

/** \brief Return the universe parameters, number of parameters and introduction rule for the given parent structure

    \pre is_structure_like(env, S)
*/
static auto get_structure_info(environment const & env, name const & S)
-> std::tuple<level_param_names, unsigned, inductive::intro_rule> {
    lean_assert(is_structure_like(env, S));
    inductive::inductive_decls idecls = *inductive::is_inductive_decl(env, S);
    inductive::intro_rule intro = head(inductive::inductive_decl_intros(head(std::get<2>(idecls))));
    return std::make_tuple(std::get<0>(idecls), std::get<1>(idecls), intro);
}

struct structure_cmd_fn {
    typedef std::unique_ptr<type_checker> type_checker_ptr;
    typedef std::vector<pair<name, name>> rename_vector;
    // field_map[i] contains the position of the \c i-th field of a parent structure into this one.
    typedef std::vector<unsigned>         field_map;
    typedef type_modifiers                modifiers;

    parser &                    m_p;
    environment                 m_env;
    name_generator              m_ngen;
    type_checker_ptr            m_tc;
    name                        m_namespace;
    name                        m_name;
    pos_info                    m_name_pos;
    buffer<name>                m_level_names;
    modifiers                   m_modifiers;
    buffer<expr>                m_params;
    expr                        m_type;
    buffer<optional<name>>      m_parent_refs;
    buffer<expr>                m_parents;
    buffer<bool>                m_private_parents;
    name                        m_mk;
    name                        m_mk_short;
    pos_info                    m_mk_pos;
    implicit_infer_kind         m_mk_infer;
    buffer<expr>                m_fields;
    std::vector<rename_vector>  m_renames;
    std::vector<field_map>      m_field_maps;
    bool                        m_infer_result_universe;
    levels                      m_ctx_levels; // context levels for creating aliases
    buffer<expr>                m_ctx_locals; // context local constants for creating aliases

    bool                        m_gen_eta;
    bool                        m_gen_proj_mk;

    structure_cmd_fn(parser & p):m_p(p), m_env(p.env()), m_ngen(p.mk_ngen()), m_namespace(get_namespace(m_env)) {
        m_tc = mk_type_checker(m_env, m_p.mk_ngen());
        m_infer_result_universe = false;
        m_gen_eta     = get_structure_eta_thm(p.get_options());
        m_gen_proj_mk = get_structure_proj_mk_thm(p.get_options());
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
        if (!m_p.curr_is_token(get_extends_tk()) && !m_p.curr_is_token(get_assign_tk()) &&
            !m_p.curr_is_token(get_colon_tk())) {
            unsigned rbp = 0;
            m_p.parse_binders(m_params, rbp);
        }
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
        if (!is_structure_like(m_env, S))
            throw parser_error(sstream() << "invalid 'structure' extends, '" << S << "' is not a structure", pos);
    }

    /** \brief Return the universe parameters, number of parameters and introduction rule for the given parent structure */
    std::tuple<level_param_names, unsigned, inductive::intro_rule> get_parent_info(name const & parent) {
        return get_structure_info(m_env, parent);
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
                bool is_private_parent = false;
                if (m_p.curr_is_token(get_private_tk())) {
                    m_p.next();
                    is_private_parent  = true;
                }
                pair<optional<name>, expr> qparent = m_p.parse_qualified_expr();
                m_parent_refs.push_back(qparent.first);
                expr const & parent = qparent.second;
                m_parents.push_back(parent);
                m_private_parents.push_back(is_private_parent);
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

    void throw_explicit_universe(pos_info const & pos) {
        throw parser_error("invalid 'structure', the resultant universe must be provided when explicit universe levels are being used", pos);
    }

    /** \brief Parse resultant universe */
    void parse_result_type() {
        auto pos = m_p.pos();
        if (m_p.curr_is_token(get_colon_tk())) {
            m_p.next();
            m_type = m_p.parse_expr();
            if (!is_sort(m_type))
                throw parser_error("invalid 'structure', 'Type' expected", pos);
            if (m_infer_result_universe) {
                if (!is_placeholder(sort_level(m_type)))
                    throw parser_error("invalid 'structure', resultant universe level is computed "
                                       "automatically when universe level parameters are not provided", pos);
            } else {
                if (has_placeholder(m_type))
                    throw_explicit_universe(pos);
                level l = sort_level(m_type);
                if (m_env.impredicative() && !is_not_zero(l))
                    throw parser_error("invalid 'structure', the resultant universe level should not be zero "
                                       "for any universe parameter assignment", pos);
            }
        } else {
            if (!m_infer_result_universe)
                throw_explicit_universe(pos);
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
            expr new_local = mk_local(mlocal_name(locals[i]), binding_name(new_tmp), binding_domain(new_tmp),
                                      binding_info(new_tmp));
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

        collected_locals dep_set;
        for (expr const & v : include_vars) {
            ::lean::collect_locals(mlocal_type(v), dep_set);
            dep_set.insert(v);
        }
        for (expr const & p : m_params)
            ::lean::collect_locals(mlocal_type(p), dep_set);
        buffer<expr> ctx;
        sort_locals(dep_set.get_collected(), m_p, ctx);

        expr tmp       = Pi_as_is(ctx, Pi(tmp_locals, m_type, m_p), m_p);
        level_param_names new_ls;
        expr new_tmp;
        std::tie(new_tmp, new_ls) = m_p.elaborate_type(tmp, list<expr>());
        levels new_meta_ls = map2<level>(new_ls, [](name const & n) { return mk_meta_univ(n); });
        new_tmp = instantiate_univ_params(new_tmp, new_ls, new_meta_ls);
        new_tmp = update_locals(new_tmp, ctx);
        new_tmp = update_locals(new_tmp, m_params);
        buffer<expr> explicit_params;
        explicit_params.append(m_params);
        m_params.clear();
        m_params.append(ctx);
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
                    throw_elaborator_exception(parent, [=](formatter const & fmt) {
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
                throw_elaborator_exception(sstream() << "invalid 'structure' header, number of argument "
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
                        throw_elaborator_exception(sstream() << "invalid 'structure' header, field '" << fname <<
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

    /** \brief Add params, fields and references to parent structures into parser local scope */
    void add_locals() {
        if (!m_infer_result_universe) {
            for (name const & l : m_level_names)
                m_p.add_local_level(l, mk_param_univ(l));
        }
        for (expr const & param : m_params)
            m_p.add_local(param);
        for (expr const & field : m_fields)
            m_p.add_local(field);
        for (unsigned i = 0; i < m_parents.size(); i++) {
            if (auto n = m_parent_refs[i]) {
                expr const & parent            = m_parents[i];
                field_map const & fmap         = m_field_maps[i];
                buffer<expr> parent_params;
                expr const & parent_fn         = get_app_args(parent, parent_params);
                levels const & parent_ls       = const_levels(parent_fn);
                name const & parent_name       = const_name(parent_fn);
                auto parent_info               = get_parent_info(parent_name);
                name const & parent_intro_name = inductive::intro_rule_name(std::get<2>(parent_info));
                expr parent_intro              = mk_app(mk_constant(parent_intro_name, parent_ls), parent_params);
                for (unsigned idx : fmap) {
                    expr const & field = m_fields[idx];
                    parent_intro = mk_app(parent_intro, field);
                }
                m_p.add_local_expr(*n, mk_as_is(parent_intro));
            }
        }
    }

    /** \brief Check if new field names collide with fields inherited from parent datastructures */
    void check_new_field_names(buffer<expr> const & new_fields) {
        for (expr const & new_field : new_fields) {
            if (std::find_if(m_fields.begin(), m_fields.end(),
                             [&](expr const & inherited_field) {
                                 return local_pp_name(inherited_field) == local_pp_name(new_field);
                             }) != m_fields.end()) {
                throw_elaborator_exception(sstream() << "field '" << local_pp_name(new_field) <<
                                           "' has been declared in parent structure",
                                           new_field);
            }
        }
    }

    void parse_field_block(buffer<expr> & new_fields, binder_info const & bi) {
        buffer<pair<pos_info, name>> names;
        while (m_p.curr_is_identifier()) {
            auto p = m_p.pos();
            names.emplace_back(p, m_p.check_atomic_id_next("invalid field, atomic identifier expected"));
        }
        if (names.empty())
            throw parser_error("invalid field, identifier expected", m_p.pos());

        m_p.check_token_next(get_colon_tk(), "invalid field, ':' expected");
        expr type = m_p.parse_expr();

        for (auto p : names) {
            expr local = m_p.save_pos(mk_local(p.second, type, bi), p.first);
            m_p.add_local(local);
            new_fields.push_back(local);
        }
    }

    /** \brief Parse new fields declared in this structure */
    void parse_new_fields(buffer<expr> & new_fields) {
        parser::local_scope scope(m_p);
        add_locals();
        while (!m_p.curr_is_command_like()) {
            if (m_p.curr_is_identifier()) {
                parse_field_block(new_fields, binder_info());
            } else {
                binder_info bi = m_p.parse_binder_info();
                parse_field_block(new_fields, bi);
                m_p.parse_close_binder_info(bi);
            }
        }
        check_new_field_names(new_fields);
    }

    /** \brief Elaborate new fields, and copy them to m_fields */
    void elaborate_new_fields(buffer<expr> & new_fields) {
        expr dummy = mk_Prop();
        unsigned j = m_parents.size();
        while (j > 0) {
            --j;
            dummy = mk_arrow(mk_as_is(m_parents[j]), dummy);
        }
        expr tmp = Pi_as_is(m_params, Pi_as_is(m_fields, Pi(new_fields, dummy, m_p), m_p), m_p);
        level_param_names new_ls;
        expr new_tmp;
        std::tie(new_tmp, new_ls) = m_p.elaborate_type(tmp, list<expr>());
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

    void process_empty_new_fields() {
        buffer<expr> new_fields;
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
        collected_locals local_set;
        ::lean::collect_locals(tmp, local_set);
        sort_locals(local_set.get_collected(), m_p, locals);
    }

    /** \brief Add context locals as extra parameters */
    void add_ctx_locals(buffer<expr> const & ctx_locals) {
        buffer<expr> params;
        params.append(m_params);
        m_params.clear();
        m_params.append(ctx_locals);
        m_params.append(params);
    }

    /** \brief Initialize m_ctx_locals field */
    void set_ctx_locals() {
        buffer<expr> new_ctx_locals;
        collect_ctx_locals(new_ctx_locals);
        add_ctx_locals(new_ctx_locals);
        for (expr const & p : m_params) {
            if (m_p.is_local_decl(p) && !m_p.is_local_variable(p))
                m_ctx_locals.push_back(p);
        }
    }

    /** \brief Include in m_level_names any local level referenced m_type and m_fields */
    void include_ctx_levels() {
        name_set all_lvl_params;
        all_lvl_params = collect_univ_params(m_type);
        for (expr const & p : m_params)
            all_lvl_params = collect_univ_params(mlocal_type(p), all_lvl_params);
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
        if (m_modifiers.is_class())
            m_env = add_class(m_env, m_name);
    }

    void save_def_info(name const & n) {
        save_info(n, "definition", m_name_pos);
    }

    void save_proj_info(name const & n) {
        save_info(n, "projection", m_name_pos);
    }

    void save_thm_info(name const & n) {
        save_info(n, "theorem", m_name_pos);
    }

    void declare_projections() {
        m_env = mk_projections(m_env, m_name, m_mk_infer, m_modifiers.is_class());
        for (expr const & field : m_fields) {
            name field_name = m_name + mlocal_name(field);
            save_proj_info(field_name);
            add_alias(field_name);
        }
    }

    void add_rec_on_alias(name const & n) {
        name rec_on_name(m_name, "rec_on");
        declaration rec_on_decl = m_env.get(rec_on_name);
        declaration new_decl = mk_definition(m_env, n, rec_on_decl.get_univ_params(),
                                             rec_on_decl.get_type(), rec_on_decl.get_value());
        m_env = module::add(m_env, check(m_env, new_decl));
        m_env = set_reducible(m_env, n, reducible_status::Reducible);
        if (list<unsigned> idx = has_unfold_hint(m_env, rec_on_name))
            m_env = add_unfold_hint(m_env, n, idx);
        save_def_info(n);
        add_alias(n);
    }

    void declare_auxiliary() {
        m_env = mk_rec_on(m_env, m_name);
        name rec_on_name(m_name, "rec_on");
        add_rec_alias(rec_on_name);
        save_def_info(rec_on_name);
        if (m_env.impredicative()) {
            m_env = mk_induction_on(m_env, m_name);
            name induction_on_name(m_name, "induction_on");
            add_rec_alias(induction_on_name);
            save_def_info(induction_on_name);
        }
        add_rec_on_alias(name(m_name, "destruct"));
        add_rec_on_alias(name(m_name, "cases_on"));
    }

    // Return the parent names without namespace prefix
    void get_truncated_parent_names(buffer<name> & parent_names) {
        for (expr const & parent : m_parents) {
            name n = const_name(get_app_fn(parent));
            if (!n.is_atomic() && n.is_string())
                n = name(n.get_string());
            parent_names.push_back(n);
        }
    }

    void mk_coercion_names(buffer<name> & coercion_names) {
        buffer<name> parent_names;
        get_truncated_parent_names(parent_names);
        name_set           found;
        name_map<unsigned> non_unique;
        for (name const & n : parent_names) {
            if (found.contains(n))
                non_unique.insert(n, 1);
            found.insert(n);
        }
        for (name & n : parent_names) {
            if (auto it = non_unique.find(n)) {
                unsigned idx = *it;
                non_unique.insert(n, idx+1);
                n = n.append_after(idx);
            }
            name coercion_name = m_name + n.append_before("to_");
            coercion_names.push_back(coercion_name);
        }
    }

    void declare_coercions() {
        lean_assert(m_parents.size() == m_field_maps.size());
        buffer<name> coercion_names;
        mk_coercion_names(coercion_names);
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
            expr coercion_value            = parent_intro;
            for (unsigned idx : fmap) {
                expr const & field = m_fields[idx];
                name proj_name = m_name + mlocal_name(field);
                expr proj      = mk_app(mk_app(mk_constant(proj_name, st_ls), m_params), st);
                coercion_value     = mk_app(coercion_value, proj);
            }
            coercion_value                 = Fun(m_params, Fun(st, coercion_value));
            name coercion_name             = coercion_names[i];
            bool use_conv_opt              = false;
            declaration coercion_decl      = mk_definition(m_env, coercion_name, lnames, coercion_type, coercion_value, use_conv_opt);
            m_env = module::add(m_env, check(m_env, coercion_decl));
            m_env = set_reducible(m_env, coercion_name, reducible_status::Reducible);
            save_def_info(coercion_name);
            add_alias(coercion_name);
            if (!m_private_parents[i]) {
                m_env = add_coercion(m_env, m_p.ios(), coercion_name);
                if (m_modifiers.is_class() && is_class(m_env, parent_name)) {
                    // if both are classes, then we also mark coercion_name as an instance
                    m_env = add_trans_instance(m_env, coercion_name);
                }
            }
        }
    }

    void declare_eta() {
        if (!m_gen_eta)
            return;
        if (!has_eq_decls(m_env))
            return;
        level_param_names lnames = to_list(m_level_names.begin(), m_level_names.end());
        levels st_ls             = param_names_to_levels(lnames);
        expr st_type             = mk_app(mk_constant(m_name, st_ls), m_params);
        expr st                  = mk_local(m_ngen.next(), "s", st_type, binder_info());
        expr lhs                 = mk_app(mk_constant(m_mk, st_ls), m_params);
        for (expr const & field : m_fields) {
            expr proj = mk_app(mk_app(mk_constant(m_name + mlocal_name(field), st_ls), m_params), st);
            lhs       = mk_app(lhs, proj);
        }
        expr eq                  = mk_app(mk_constant(get_eq_name(), to_list(sort_level(m_type))), st_type, lhs, st);
        level eq_lvl             = sort_level(m_tc->ensure_type(eq).first);
        levels rec_ls            = levels(eq_lvl, st_ls);
        expr rec                 = mk_app(mk_constant(inductive::get_elim_name(m_name), rec_ls), m_params);
        expr type_former         = Fun(st, eq);
        expr mk                  = mk_app(mk_app(mk_constant(m_mk, st_ls), m_params), m_fields);
        expr refl                = mk_app(mk_constant(get_eq_refl_name(), to_list(sort_level(m_type))), st_type, mk);
        refl                     = Fun(m_fields, refl);
        rec                      = mk_app(rec, type_former, refl, st);
        expr eta_type            = infer_implicit(Pi(m_params, Pi(st, eq)), true);
        expr eta_value           = Fun(m_params, Fun(st, rec));
        name eta_name(m_name, "eta");

        declaration eta_decl     = mk_theorem(m_env, eta_name, lnames, eta_type, eta_value);
        m_env = module::add(m_env, check(m_env, eta_decl));
        save_thm_info(eta_name);
        add_alias(eta_name);
    }

    void declare_proj_over_mk() {
        if (!m_gen_proj_mk)
            return;
        if (!has_eq_decls(m_env))
            return;
        level_param_names lnames = to_list(m_level_names.begin(), m_level_names.end());
        levels st_ls             = param_names_to_levels(lnames);
        expr st_type             = mk_app(mk_constant(m_name, st_ls), m_params);
        expr mk_fields           = mk_app(mk_app(mk_constant(m_mk, st_ls), m_params), m_fields);
        for (unsigned i = 0; i < m_fields.size(); i++) {
            expr const & field      = m_fields[i];
            name const & field_name = mlocal_name(field);
            expr const & field_type = mlocal_type(field);
            if (m_env.prop_proof_irrel() && m_tc->is_prop(field_type).first)
                continue;
            level field_level       = sort_level(m_tc->ensure_type(field_type).first);
            name proj_name          = m_name + field_name;
            expr lhs                = mk_app(mk_app(mk_constant(proj_name, st_ls), m_params), mk_fields);
            expr rhs                = field;
            expr eq                 = mk_app(mk_constant(get_eq_name(), to_list(field_level)), field_type, lhs, rhs);
            expr refl               = mk_app(mk_constant(get_eq_refl_name(), to_list(field_level)), field_type, lhs);
            name proj_over_name     = m_name + field_name + m_mk_short;
            expr proj_over_type     = infer_implicit(Pi(m_params, Pi(m_fields, eq)), m_params.size(), true);
            expr proj_over_value    = Fun(m_params, Fun(m_fields, refl));

            declaration proj_over_decl = mk_theorem(m_env, proj_over_name, lnames, proj_over_type, proj_over_value);
            m_env = module::add(m_env, check(m_env, proj_over_decl));
            save_thm_info(proj_over_name);
            add_alias(proj_over_name);
        }
    }

    void declare_no_confustion() {
        if (!has_eq_decls(m_env))
            return;
        if (m_env.impredicative() && !has_heq_decls(m_env))
            return;
        if (!m_env.impredicative() && !has_lift_decls(m_env))
            return;
        m_env = mk_no_confusion(m_env, m_name);
        name no_confusion_name(m_name, "no_confusion");
        save_def_info(no_confusion_name);
        add_alias(no_confusion_name);
    }

    environment operator()() {
        process_header();
        if (m_p.curr_is_token(get_assign_tk())) {
            m_p.check_token_next(get_assign_tk(), "invalid 'structure', ':=' expected");
            m_mk_pos = m_p.pos();
            if (m_p.curr_is_token(get_lparen_tk()) || m_p.curr_is_token(get_lcurly_tk()) ||
                m_p.curr_is_token(get_lbracket_tk())) {
                m_mk_short = LEAN_DEFAULT_STRUCTURE_INTRO;
                m_mk_infer = implicit_infer_kind::Implicit;
            } else {
                m_mk_short = m_p.check_atomic_id_next("invalid 'structure', identifier expected");
                m_mk_infer = parse_implicit_infer_modifier(m_p);
                if (!m_p.curr_is_command_like())
                    m_p.check_token_next(get_dcolon_tk(), "invalid 'structure', '::' expected");
            }
            m_mk = m_name + m_mk_short;
            process_new_fields();
        } else {
            m_mk_pos   = m_name_pos;
            m_mk_short = LEAN_DEFAULT_STRUCTURE_INTRO;
            m_mk_infer = implicit_infer_kind::Implicit;
            m_mk       = m_name + m_mk_short;
            process_empty_new_fields();
        }
        infer_resultant_universe();
        set_ctx_locals();
        include_ctx_levels();
        m_ctx_levels = collect_local_nonvar_levels(m_p, to_list(m_level_names.begin(), m_level_names.end()));
        declare_inductive_type();
        declare_projections();
        declare_auxiliary();
        declare_coercions();
        declare_eta();
        declare_proj_over_mk();
        declare_no_confustion();
        return m_env;
    }
};

environment structure_cmd(parser & p) {
    return structure_cmd_fn(p)();
}

void get_structure_fields(environment const & env, name const & S, buffer<name> & fields) {
    lean_assert(is_structure_like(env, S));
    level_param_names ls; unsigned nparams; inductive::intro_rule intro;
    std::tie(ls, nparams, intro) = get_structure_info(env, S);
    expr intro_type = inductive::intro_rule_type(intro);
    unsigned i = 0;
    while (is_pi(intro_type)) {
        if (i >= nparams)
            fields.push_back(S + binding_name(intro_type));
        i++;
        intro_type = binding_body(intro_type);
    }
}

bool is_structure(environment const & env, name const & S) {
    if (!is_structure_like(env, S))
        return false;
    level_param_names ls; unsigned nparams; inductive::intro_rule intro;
    std::tie(ls, nparams, intro) = get_structure_info(env, S);
    expr intro_type = inductive::intro_rule_type(intro);
    for (unsigned i = 0; i < nparams; i++) {
        if (!is_pi(intro_type))
            return false;
        intro_type = binding_body(intro_type);
    }
    if (!is_pi(intro_type))
        return false;
    name field_name = S + binding_name(intro_type);
    return get_projection_info(env, field_name) != nullptr;
}

static name * g_structure_instance_name          = nullptr;
static std::string * g_structure_instance_opcode = nullptr;

void register_structure_cmd(cmd_table & r) {
    add_cmd(r, cmd_info("structure",   "declare a new structure/record type", structure_cmd));
}

[[ noreturn ]] static void throw_se_ex() { throw exception("unexpected occurrence of 'structure instance' expression"); }

// We encode a 'structure instance' expression using a macro.
// This is a trick to avoid creating a new kind of expression.
// 'Structure instance' expressions are temporary objects used by the elaborator.
// Example: Given
//     structure point (A B : Type) := (x : A) (y : B)
// the structure instance
//     {| point, x := 10, y := 20 |}
// is compiled into
//     point.mk 10 20
class structure_instance_macro_cell : public macro_definition_cell {
    list<name> m_fields;
public:
    structure_instance_macro_cell(list<name> const & fs):m_fields(fs) {}
    virtual name get_name() const { return *g_structure_instance_name; }
    virtual pair<expr, constraint_seq> check_type(expr const &, extension_context &, bool) const { throw_se_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_se_ex(); }
    virtual void write(serializer & s) const {
        s << *g_structure_instance_opcode;
        write_list(s, m_fields);
    }
    list<name> const & get_field_names() const { return m_fields; }
};

static expr mk_structure_instance(list<name> const & fs, unsigned num, expr const * args) {
    lean_assert(num >= length(fs) + 1);
    macro_definition def(new structure_instance_macro_cell(fs));
    return mk_macro(def, num, args);
}

bool is_structure_instance(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == *g_structure_instance_name;
}

void destruct_structure_instance(expr const & e, expr & t, buffer<name> & field_names,
                                 buffer<expr> & field_values, buffer<expr> & using_exprs) {
    lean_assert(is_structure_instance(e));
    t = macro_arg(e, 0);
    list<name> const & fns = static_cast<structure_instance_macro_cell const*>(macro_def(e).raw())->get_field_names();
    unsigned num_fileds = length(fns);
    to_buffer(fns, field_names);
    for (unsigned i = 1; i < num_fileds+1; i++)
        field_values.push_back(macro_arg(e, i));
    for (unsigned i = num_fileds+1; i < macro_num_args(e); i++)
        using_exprs.push_back(macro_arg(e, i));
}

static expr parse_struct_expr_core(parser & p, pos_info const & pos, bool curly_bar) {
    expr t = p.parse_expr();
    buffer<name> field_names;
    buffer<expr> field_values;
    buffer<expr> using_exprs;
    while (p.curr_is_token(get_comma_tk())) {
        p.next();
        pair<optional<name>, expr> id_e = p.parse_optional_assignment();
        if (id_e.first) {
            field_names.push_back(*id_e.first);
            field_values.push_back(id_e.second);
        } else {
            using_exprs.push_back(id_e.second);
        }
    }
    if (curly_bar)
        p.check_token_next(get_rcurlybar_tk(), "invalid structure expression, '|}' expected");
    else
        p.check_token_next(get_rdcurly_tk(), "invalid structure expression, '⦄' expected");
    buffer<expr> args;
    args.push_back(t);
    args.append(field_values);
    args.append(using_exprs);
    return p.save_pos(mk_structure_instance(to_list(field_names), args.size(), args.data()), pos);
}

static expr parse_struct_curly_bar(parser & p, unsigned, expr const *, pos_info const & pos) {
    bool curly_bar = true;
    return parse_struct_expr_core(p, pos, curly_bar);
}

static expr parse_struct_dcurly(parser & p, unsigned, expr const *, pos_info const & pos) {
    bool curly_bar = false;
    return parse_struct_expr_core(p, pos, curly_bar);
}

void init_structure_instance_parsing_rules(parse_table & r) {
    expr x0 = mk_var(0);
    r = r.add({notation::transition("{|", notation::mk_ext_action(parse_struct_curly_bar))}, x0);
    r = r.add({notation::transition("⦃",  notation::mk_ext_action(parse_struct_dcurly))}, x0);
}

void initialize_structure_cmd() {
    g_tmp_prefix  = new name(name::mk_internal_unique_name());
    g_gen_eta     = new name{"structure", "eta_thm"};
    g_gen_proj_mk = new name{"structure", "proj_mk_thm"};
    register_bool_option(*g_gen_eta, LEAN_DEFAULT_STRUCTURE_ETA,
                         "(structure) automatically generate 'eta' theorem whenever declaring a new structure");
    register_bool_option(*g_gen_proj_mk, LEAN_DEFAULT_STRUCTURE_PROJ_MK,
                         "(structure) automatically gneerate projection over introduction theorem when "
                         "declaring a new structure, the theorem is never generated for proof irrelevant fields");
    g_structure_instance_name   = new name("structure instance");
    g_structure_instance_opcode = new std::string("STI");
    register_macro_deserializer(*g_structure_instance_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    list<name> fs;
                                    fs = read_list<name>(d);
                                    if (num < length(fs) + 1)
                                        throw corrupted_stream_exception();
                                    return mk_structure_instance(fs, num, args);
                                });
}

void finalize_structure_cmd() {
    delete g_tmp_prefix;
    delete g_gen_eta;
    delete g_gen_proj_mk;
    delete g_structure_instance_opcode;
    delete g_structure_instance_name;
}
}
