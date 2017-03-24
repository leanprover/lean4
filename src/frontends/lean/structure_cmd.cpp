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
#include "util/fresh_name.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "kernel/error_msgs.h"
#include "kernel/inductive/inductive.h"
#include "library/trace.h"
#include "library/attribute_manager.h"
#include "library/scoped_ext.h"
#include "library/normalize.h"
#include "library/placeholder.h"
#include "library/locals.h"
#include "library/reducible.h"
#include "library/module.h"
#include "library/aliases.h"
#include "library/annotation.h"
#include "library/explicit.h"
#include "library/unfold_macros.h"
#include "library/protected.h"
#include "library/private.h"
#include "library/class.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/projection.h"
#include "library/aux_recursors.h"
#include "library/kernel_serializer.h"
#include "library/type_context.h"
#include "library/app_builder.h"
#include "library/documentation.h"
#include "library/compiler/vm_compiler.h"
#include "library/constructions/rec_on.h"
#include "library/constructions/cases_on.h"
#include "library/constructions/projection.h"
#include "library/constructions/no_confusion.h"
#include "library/constructions/injective.h"
#include "library/inductive_compiler/add_decl.h"
#include "library/tactic/elaborator_exception.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/type_util.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/inductive_cmds.h"

#ifndef LEAN_DEFAULT_STRUCTURE_INTRO
#define LEAN_DEFAULT_STRUCTURE_INTRO "mk"
#endif

namespace lean {
/** \brief Return the universe parameters, number of parameters and introduction rule for the given parent structure

    \pre is_structure_like(env, S) */
static auto get_structure_info(environment const & env, name const & S)
-> std::tuple<level_param_names, unsigned, inductive::intro_rule> {
    lean_assert(is_structure_like(env, S));
    inductive::inductive_decl idecl = *inductive::is_inductive_decl(env, S);
    inductive::intro_rule intro = head(idecl.m_intro_rules);
    return std::make_tuple(idecl.m_level_params, idecl.m_num_params, intro);
}

optional<name> has_default_value(environment const & env, name const & full_field_name) {
    name default_name(full_field_name, "_default");
    if (env.find(default_name))
        return optional<name>(default_name);
    else
        return optional<name>();
}

expr mk_field_default_value(environment const & env, name const & full_field_name, std::function<optional<expr>(name const &)> const & get_field_value) {
    optional<name> default_name = has_default_value(env, full_field_name);
    lean_assert(default_name);
    declaration decl = env.get(*default_name);
    expr value = decl.get_value();
    buffer<expr> args;
    while (is_lambda(value)) {
        if (is_explicit(binding_info(value))) {
            name fname = binding_name(value);
            optional<expr> fval = get_field_value(fname);
            if (!fval) {
                throw exception(sstream() << "failed to construct default value for '" << full_field_name << "', "
                                << "it depends on field '" << fname << "', but the value for this field is not available");
            }
            args.push_back(*fval);
        } else {
            args.push_back(mk_expr_placeholder());
        }
        value = binding_body(value);
    }
    return mk_app(mk_explicit(mk_constant(*default_name)), args);
}

struct structure_cmd_fn {
    typedef std::vector<pair<name, name>> rename_vector;
    // field_map[i] contains the position of the \c i-th field of a parent structure into this one.
    typedef std::vector<unsigned>         field_map;
    struct field_decl {
        expr local; // name, type, and pos as an expr::local
        optional<expr> default_val;
        bool from_parent;
        bool explicit_type;
    };

    parser &                    m_p;
    decl_modifiers              m_modifiers;
    environment                 m_env;
    type_context                m_ctx;
    name                        m_namespace;
    name                        m_name;
    name                        m_given_name;
    optional<std::string>       m_doc_string;
    pos_info                    m_name_pos;
    buffer<name>                m_level_names;
    decl_attributes             m_attrs;
    buffer<expr>                m_params;
    expr                        m_type;
    buffer<optional<name>>      m_parent_refs;
    buffer<expr>                m_parents;
    buffer<bool>                m_private_parents;
    name                        m_mk;
    name                        m_mk_short;
    pos_info                    m_mk_pos;
    implicit_infer_kind         m_mk_infer;
    buffer<field_decl>          m_fields;
    std::vector<rename_vector>  m_renames;
    std::vector<field_map>      m_field_maps;
    bool                        m_explicit_universe_params;
    bool                        m_infer_result_universe;
    bool                        m_inductive_predicate;
    levels                      m_ctx_levels; // context levels for creating aliases
    buffer<expr>                m_ctx_locals; // context local constants for creating aliases
    unsigned                    m_prio;

    structure_cmd_fn(parser & p, decl_attributes const & attrs, decl_modifiers const & modifiers):
        m_p(p),
        m_modifiers(modifiers),
        m_env(p.env()),
        m_ctx(p.env()),
        m_namespace(get_namespace(m_env)),
        m_attrs(attrs) {
        m_explicit_universe_params = false;
        m_infer_result_universe    = false;
        m_inductive_predicate      = false;
        m_prio                     = get_default_priority(p.get_options());
        m_doc_string               = p.get_doc_string();
    }

    void check_attrs(decl_attributes const & attrs, pos_info const & pos) const {
        if (!attrs.ok_for_inductive_type())
            throw parser_error("only attribute [class] accepted for structures", pos);
    }

    /** \brief Parse structure name and (optional) universe parameters */
    void parse_decl_name() {
        m_name_pos = m_p.pos();
        m_attrs.parse(m_p);
        check_attrs(m_attrs, m_name_pos);
        buffer<name> ls_buffer;
        if (parse_univ_params(m_p, ls_buffer)) {
            m_explicit_universe_params = true;
            m_level_names.append(ls_buffer);
        } else {
            m_explicit_universe_params = false;
        }
        m_given_name = m_p.check_decl_id_next("invalid 'structure', identifier expected");
        if (m_modifiers.m_is_private) {
            unsigned h   = hash(m_name_pos.first, m_name_pos.second);
            auto env_n   = add_private_name(m_env, m_given_name, optional<unsigned>(h));
            m_env        = env_n.first;
            m_name  = env_n.second;
        } else {
            m_name = m_namespace + m_given_name;
        }
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

    /** \brief Parse resultant universe */
    void parse_result_type() {
        auto pos = m_p.pos();
        if (m_p.curr_is_token(get_colon_tk())) {
            m_p.next();
            m_type = m_p.parse_expr();
            while (is_annotation(m_type))
                m_type = get_annotation_arg(m_type);
            if (!is_sort(m_type))
                throw parser_error("invalid 'structure', 'Type' expected", pos);
            m_inductive_predicate = is_zero(sort_level(m_type));
            if (m_inductive_predicate) {
                m_infer_result_universe = false;
            } else if (is_one_placeholder(sort_level(m_type))) {
                m_infer_result_universe = false;
                m_type = m_p.save_pos(mk_sort(mk_level_one()), pos);
            } else {
                m_infer_result_universe = is_placeholder(sort_level(m_type));
                if (!m_infer_result_universe) {
                    if (!is_zero(sort_level(m_type)) && !is_not_zero(sort_level(m_type)))
                        throw parser_error("invalid universe polymorphic structure declaration, "
                                           "the resultant universe is not Prop (i.e., 0), "
                                           "but it may be Prop for some parameter values "
                                           "(solution: use 'l+1' or 'max 1 l')", m_p.pos());
                }
            }
        } else {
            m_infer_result_universe = true;
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
            if (!is_binding(new_tmp))
                throw exception("structure command elaboration was interrupted due to nested errors");
            expr new_local = mk_local(mlocal_name(locals[i]), binding_name(new_tmp), binding_domain(new_tmp),
                                      binding_info(new_tmp));
            locals[i]      = new_local;
            new_tmp        = instantiate(binding_body(new_tmp), new_local);
        }
        return new_tmp;
    }

    expr update_default_values(expr new_tmp, buffer<field_decl> & decls) {
        for (auto & decl : decls) {
            if (decl.default_val && decl.explicit_type) {
                lean_assert(is_let(new_tmp));
                decl.default_val = let_value(new_tmp);
                new_tmp          = let_body(new_tmp);
            }
        }
        return new_tmp;
    }

    expr update_fields(expr new_tmp, buffer<field_decl> & decls) {
        for (auto & decl : decls) {
            if (decl.default_val && !decl.explicit_type) {
                    lean_assert(is_let(new_tmp));
                    expr new_local   = mk_local(mlocal_name(decl.local), let_name(new_tmp), let_type(new_tmp), {});
                    decl.local       = new_local;
                    decl.default_val = let_value(new_tmp);
                    new_tmp          = instantiate(let_body(new_tmp), new_local);
            } else {
                lean_assert(is_pi(new_tmp));
                expr new_local = mk_local(mlocal_name(decl.local), binding_name(new_tmp), binding_domain(new_tmp),
                                          binding_info(new_tmp));
                decl.local     = new_local;
                new_tmp        = instantiate(binding_body(new_tmp), new_local);
            }
        }
        return new_tmp;
    }

    expr update_parents(expr new_tmp, bool inst) {
        for (unsigned i = 0; i < m_parents.size(); i++) {
            m_parents[i]   = copy_tag(m_parents[i], expr(binding_domain(new_tmp)));
            new_tmp        = binding_body(new_tmp);
            if (inst)
                new_tmp = instantiate(new_tmp, mk_parent_expr(i));
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
            tmp_locals.push_back(mk_local(mk_fresh_name(), parent));

        collected_locals dep_set;
        for (expr const & v : include_vars) {
            ::lean::collect_locals(mlocal_type(v), dep_set);
            dep_set.insert(v);
        }
        for (expr const & p : m_params)
            ::lean::collect_locals(mlocal_type(p), dep_set);
        collect_annonymous_inst_implicit(m_p, dep_set);
        /* Copy the locals from dep_set that are NOT in m_params to dep_set_minus_params */
        buffer<expr> dep_set_minus_params;
        for (auto d : dep_set.get_collected()) {
            if (std::all_of(m_params.begin(), m_params.end(), [&](expr const & p) { return mlocal_name(d) != mlocal_name(p); }))
                dep_set_minus_params.push_back(d);
        }
        /* Sort dep_set_minus_params and store result in ctx */
        buffer<expr> ctx;
        sort_locals(dep_set_minus_params, m_p, ctx);

        expr tmp       = Pi_as_is(ctx, Pi(tmp_locals, m_type, m_p), m_p);
        level_param_names new_ls;
        expr new_tmp;
        std::tie(new_tmp, new_ls) = m_p.elaborate_type(m_name, list<expr>(), tmp);
        levels new_meta_ls = map2<level>(new_ls, [&](name const &) { return m_ctx.mk_univ_metavar_decl(); });
        new_tmp = instantiate_univ_params(new_tmp, new_ls, new_meta_ls);
        new_tmp = update_locals(new_tmp, ctx);
        new_tmp = update_locals(new_tmp, m_params);
        buffer<expr> explicit_params;
        explicit_params.append(m_params);
        m_params.clear();
        m_params.append(ctx);
        m_params.append(explicit_params);
        new_tmp = update_parents(new_tmp, false);
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
    optional<unsigned> merge(expr const & parent, name const & fname, expr const & ftype) {
        for (unsigned i = 0; i < m_fields.size(); i++) {
            if (local_pp_name(m_fields[i].local) == fname) {
                if (m_ctx.is_def_eq(mlocal_type(m_fields[i].local), ftype)) {
                    return optional<unsigned>(i);
                } else {
                    expr prev_ftype = mlocal_type(m_fields[i].local);
                    throw generic_exception(parent, [=](formatter const & fmt) {
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

    expr mk_field_default_value(name const & full_field_name) {
        return ::lean::mk_field_default_value(m_env, full_field_name, [&](name const & fname) {
                for (field_decl const & d : m_fields) {
                    if (local_pp_name(d.local) == fname)
                        return some_expr(mk_explicit(d.local));
                }
                return none_expr();
            });
    }

    /** \brief Process extends clauses.
        This method also populates the vector m_field_maps and m_fields. */
    void process_extends() {
        lean_assert(m_fields.empty());
        lean_assert(m_field_maps.empty());
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
                throw elaborator_exception(parent,
                                           sstream() << "invalid 'structure' header, number of argument "
                                           "mismatch for parent structure '" << parent_name << "'");
            }
            for (expr const & arg : args) {
                if (!is_pi(intro_type))
                    throw_ill_formed_parent(parent_name);
                intro_type = instantiate(binding_body(intro_type), arg);
            }
            size_t fmap_start = fmap.size();
            while (is_pi(intro_type)) {
                name fname = binding_name(intro_type);
                fname      = rename(renames, fname);
                expr const & ftype = binding_domain(intro_type);
                name full_fname = parent_name + fname;
                expr field;
                if (auto fidx = merge(parent, fname, ftype)) {
                    fmap.push_back(*fidx);
                    field = m_fields[*fidx].local;
                    if (local_info(field) != binding_info(intro_type)) {
                        throw elaborator_exception(parent,
                                                   sstream() << "invalid 'structure' header, field '" << fname <<
                                                   "' has already been declared with a different binder annotation");
                    }
                } else {
                    field = mk_local(fname, ftype, binding_info(intro_type));
                    fmap.push_back(m_fields.size());
                    m_fields.push_back({field, none_expr(), /* from_parent */ true, /* explicit_type */ true});
                }
                intro_type = instantiate(binding_body(intro_type), field);
            }
            // construct and add default values now that all fields have been defined
            for (size_t fmap_idx = fmap_start; fmap_idx < fmap.size(); fmap_idx++) {
                field_decl & field = m_fields[fmap[fmap_start]];
                name fname = local_pp_name(field.local);
                name full_fname = parent_name + fname;
                if (optional<name> fdefault_name = has_default_value(m_env, full_fname)) {
                    expr fdefault = mk_field_default_value(full_fname);
                    if (!field.default_val) {
                        field.default_val = fdefault;
                    } else if (field.default_val && !m_ctx.is_def_eq(*field.default_val, fdefault)) {
                        expr prev_default = *field.default_val;
                        throw generic_exception(parent, [=](formatter const &fmt) {
                            format r = format("invalid 'structure' header, field '");
                            r += format(fname);
                            r += format("' from '");
                            r += format(const_name(get_app_fn(parent)));
                            r += format("' has already been declared with a different default value");
                            r += pp_indent_expr(fmt, prev_default);
                            r += compose(line(), format("and"));
                            r += pp_indent_expr(fmt, fdefault);
                            return r;
                        });
                    }
                }
                fmap_start++;
            }
        }
        lean_assert(m_parents.size() == m_field_maps.size());
    }

    void instantiate_mvars() {
        for (expr & parent : m_parents)
            parent = m_ctx.instantiate_mvars(parent);
        for (expr & param : m_params)
            param = m_ctx.instantiate_mvars(param);
        for (field_decl & decl : m_fields) {
            decl.local  = m_ctx.instantiate_mvars(decl.local);
            if (decl.default_val)
                decl.default_val = m_ctx.instantiate_mvars(*decl.default_val);
        }
    }

    /** \brief Parse header, elaborate it, and process parents (aka extends clauses) */
    void process_header() {
        parse_header();
        elaborate_header();
        process_extends();
        instantiate_mvars();
    }

    /** \brief Create expression of type \c m_parents[i] from corresponding fields */
    expr mk_parent_expr(unsigned i) {
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
            expr const & field = m_fields[idx].local;
            parent_intro = mk_app(parent_intro, field);
        }
        return parent_intro;
    }

    /** \brief Add params, fields and references to parent structures into parser local scope */
    void add_locals() {
        if (m_explicit_universe_params) {
            for (name const & l : m_level_names)
                m_p.add_local_level(l, mk_param_univ(l));
        }
        for (expr const & param : m_params)
            m_p.add_local(param);
        for (field_decl const & decl : m_fields)
            m_p.add_local(decl.local);
        for (unsigned i = 0; i < m_parents.size(); i++) {
            if (auto n = m_parent_refs[i])
                m_p.add_local_expr(*n, mk_as_is(mk_parent_expr(i)));
        }
    }

    field_decl * get_field_by_name(name const & name) {
        auto it = std::find_if(m_fields.begin(), m_fields.end(), [&](field_decl const & inherited_field) {
            return local_pp_name(inherited_field.local) == name;
        });
        return it != m_fields.end() ? it : nullptr;
    }

    void parse_field_block(binder_info const & bi) {
        buffer<pair<pos_info, name>> names;
        auto start_pos = m_p.pos();
        while (m_p.curr_is_identifier()) {
            auto p = m_p.pos();
            names.emplace_back(p, m_p.check_atomic_id_next("invalid field, atomic identifier expected"));
        }
        if (names.empty())
            throw parser_error("invalid field, identifier expected", m_p.pos());

        expr type;
        optional<expr> default_value;
        if (m_p.curr_is_token(get_assign_tk())) {
            type = m_p.save_pos(mk_expr_placeholder(), m_p.pos());
            m_p.next();
            default_value = m_p.parse_expr();
        } else {
            m_p.check_token_next(get_colon_tk(), "invalid field, ':' expected");
            type = m_p.parse_expr();
            if (m_p.curr_is_token(get_assign_tk())) {
                m_p.next();
                default_value = m_p.parse_expr();
            } else if (m_p.curr_is_token(get_period_tk())) {
                type = parse_auto_param(m_p, type);
            }
        }
        if (default_value && !is_explicit(bi)) {
            throw parser_error("invalid field, it is not explicit, but it has a default value", start_pos);
        }
        for (auto p : names) {
            if (auto old_field = get_field_by_name(p.second)) {
                if (is_placeholder(type)) {
                    old_field->default_val = default_value;
                } else {
                    sstream msg;
                    msg << "field '" << p.second;
                    if (old_field->from_parent)
                        msg << "' has been declared in parent structure";
                    else
                        msg <<"' has already been declared";
                    if (default_value)
                        msg << " (omit its type to set a new default value)";
                    throw parser_error(msg, start_pos);
                }
            } else {
                expr local = m_p.save_pos(mk_local(p.second, type, bi), p.first);
                m_p.add_local(local);
                m_fields.push_back({local, default_value, /* from_parent */ false, /* explicit_type */ !is_placeholder(type)});
            }
        }
    }

    /** \brief Parse new fields declared in this structure */
    void parse_new_fields() {
        parser::local_scope scope(m_p);
        add_locals();
        while (!m_p.curr_is_command_like()) {
            if (m_p.curr_is_identifier()) {
                parse_field_block(binder_info());
            } else {
                binder_info bi = m_p.parse_binder_info();
                if (!m_p.parse_local_notation_decl())
                    parse_field_block(bi);
                m_p.parse_close_binder_info(bi);
            }
        }
    }

    expr mk_field_binder(buffer<field_decl> const & decls, expr const & type,
                         bool typed_defaults_only = false) {
        expr r = type;
        unsigned i = decls.size();
        while (i > 0) {
            --i;
            field_decl const & decl = decls[i];
            if (decl.default_val && (typed_defaults_only == decl.explicit_type)) {
                expr type  = mlocal_type(decl.local);
                expr value = *decl.default_val;
                if (decl.from_parent) {
                    type  = mk_as_is(type);
                }
                if (typed_defaults_only)
                    r = mk_let(mk_fresh_name(), type, value, r);
                else
                    r = mk_let(local_pp_name(decl.local), type, value, abstract_local(r, decl.local));
            } else if (!typed_defaults_only) {
                if (decl.from_parent) {
                    r = Pi_as_is(decl.local, r);
                } else {
                    r = Pi(decl.local, r);
                }
            }
        }
        return r;
    }

    /** \brief Elaborate new fields */
    void elaborate_new_fields() {
        // start with typed default values so that they can depend on any field
        expr tmp = mk_field_binder(m_fields, mk_Prop(), true);
        tmp = mk_field_binder(m_fields, tmp, false);
        unsigned j = m_parents.size();
        while (j > 0) {
            --j;
            tmp = mk_arrow(mk_as_is(m_parents[j]), tmp);
        }
        tmp = Pi_as_is(m_params, tmp, m_p);
        level_param_names new_ls;
        expr new_tmp;
        metavar_context mctx      = m_ctx.mctx();
        std::tie(new_tmp, new_ls) = m_p.elaborate_type(m_name, mctx, tmp);
        m_ctx.set_mctx(mctx);
        for (auto new_l : new_ls)
            m_level_names.push_back(new_l);
        new_tmp = update_locals(new_tmp, m_params);
        new_tmp = update_parents(new_tmp, true);
        new_tmp = update_fields(new_tmp, m_fields);
        new_tmp = update_default_values(new_tmp, m_fields);
        lean_assert(new_tmp == mk_Prop());
    }

    /** \brief Parse new fields declared by this structure, and elaborate them. */
    void process_new_fields() {
        parse_new_fields();
        elaborate_new_fields();
    }

    void process_empty_new_fields() {
        elaborate_new_fields();
    }

    /** \brief Traverse fields and collect the universes they reside in \c r_lvls.
        This information is used to compute the resultant universe level for the inductive datatype declaration. */
    void accumulate_levels(buffer<level> & r_lvls) {
        for (field_decl const & decl : m_fields) {
            level l = get_level(m_ctx, mlocal_type(decl.local));
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
            level r_lvl = mk_result_level(r_lvls);
            m_type      = mk_sort(r_lvl);
        }
    }

    /** \brief Display m_fields (for debugging purposes) */
    void display_fields(std::ostream & out) {
        for (field_decl const & decl : m_fields) {
            out << ">> " << mlocal_name(decl.local) << " : " << mlocal_type(decl.local);
            if (decl.default_val)
                out << " := " << *decl.default_val;
            out << "\n";
        }
    }

    /** \brief Collect context local constants used in the declaration. */
    void collect_ctx_locals(buffer<expr> & locals) {
        if (!m_p.has_locals())
            return;
        expr dummy = mk_Prop();
        expr tmp   = Pi(m_params, mk_field_binder(m_fields, dummy));
        collected_locals local_set;
        ::lean::collect_locals(tmp, local_set);
        collect_annonymous_inst_implicit(m_p, local_set);
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
        for (field_decl const & f : m_fields) {
            all_lvl_params = collect_univ_params(mlocal_type(f.local), all_lvl_params);
            if (f.default_val)
                all_lvl_params = collect_univ_params(*f.default_val, all_lvl_params);
        }
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
        return Pi(m_params, m_type, m_p);
    }

    expr mk_structure_type_no_params() {
        return m_type;
    }

    expr mk_intro_type() {
        levels ls = param_names_to_levels(to_list(m_level_names.begin(), m_level_names.end()));
        expr r    = mk_app(mk_constant(m_name, ls), m_params);
        buffer<expr> field_wo_defaults;
        for (field_decl const & decl : m_fields) field_wo_defaults.push_back(decl.local);
        r         = Pi(m_params, Pi(field_wo_defaults, r, m_p), m_p);
        return infer_implicit_params(r, m_params.size(), m_mk_infer);
    }

    expr mk_intro_type_no_params() {
        levels ls = param_names_to_levels(to_list(m_level_names.begin(), m_level_names.end()));
        expr r    = mk_app(mk_constant(m_name, ls), m_params);
        buffer<expr> field_wo_defaults;
        for (field_decl const & decl : m_fields) field_wo_defaults.push_back(decl.local);
        r         = Pi(field_wo_defaults, r, m_p);
        return r;
    }

    void add_alias(name const & given, name const & n) {
        m_env = ::lean::add_alias(m_p, m_env, given, n, m_ctx_levels, m_ctx_locals);
    }

    void add_alias(name const & n, bool composite = true) {
        m_env = ::lean::add_alias(m_p, m_env, composite, n, m_ctx_levels, m_ctx_locals);
    }

    void add_rec_alias(name const & n) {
        levels rec_ctx_levels;
        if (!is_nil(m_ctx_levels))
            rec_ctx_levels = levels(mk_level_placeholder(), m_ctx_levels);
        if (m_modifiers.m_is_private) {
            name given_rec_name = name(m_given_name, n.get_string());
            m_env = ::lean::add_alias(m_p, m_env, given_rec_name, n, rec_ctx_levels, m_ctx_locals);
        } else {
            bool composite = true;
            m_env = ::lean::add_alias(m_p, m_env, composite, n, rec_ctx_levels, m_ctx_locals);
        }
    }

    void declare_inductive_type() {
        expr structure_type = mk_structure_type();
        expr intro_type     = mk_intro_type();

        level_param_names lnames = to_list(m_level_names.begin(), m_level_names.end());
        inductive::intro_rule intro = inductive::mk_intro_rule(m_mk, intro_type);
        inductive::inductive_decl  decl(m_name, lnames, m_params.size(), structure_type, to_list(intro));
        bool is_trusted = !m_modifiers.m_is_meta;
        m_env = module::add_inductive(m_env, decl, is_trusted);
        name rec_name = inductive::get_elim_name(m_name);
        m_env = add_namespace(m_env, m_name);
        m_env = add_protected(m_env, rec_name);
        add_alias(m_given_name, m_name);
        add_alias(m_mk);
        add_rec_alias(rec_name);
        m_env = m_attrs.apply(m_env, m_p.ios(), m_name);

        m_env = add_structure_declaration_aux(m_env, m_p.get_options(), m_level_names, m_params,
                                              mk_local(m_name, mk_structure_type_no_params()),
                                              mk_local(m_mk, mk_intro_type_no_params()));
    }

    void declare_projections() {
        m_env = mk_projections(m_env, m_name, m_mk_infer, m_attrs.has_class());
        for (field_decl const & field : m_fields) {
            name field_name = m_name + mlocal_name(field.local);
            add_alias(field_name);
        }
    }

    bool is_field(expr const & local) {
        for (field_decl const & field : m_fields) {
            if (mlocal_name(field.local) == mlocal_name(local))
                return true;
        }
        return false;
    }

    void declare_defaults() {
        for (field_decl const & field : m_fields) {
            if (field.default_val) {
                collected_locals used_locals;
                collect_locals(mlocal_type(field.local), used_locals);
                collect_locals(*field.default_val, used_locals);
                buffer<expr> args;
                /* Copy params first */
                for (expr const & local : used_locals.get_collected()) {
                    if (!is_field(local)) {
                        if (is_explicit(local_info(local)))
                            args.push_back(update_local(local, mk_implicit_binder_info()));
                        else
                            args.push_back(local);
                    }
                }
                /* Copy fields it depends on */
                for (expr const & local : used_locals.get_collected()) {
                    if (is_field(local))
                        args.push_back(local);
                }
                name decl_name  = name(m_name + local_pp_name(field.local), "_default");
                /* TODO(Leo): add helper function for adding definition.
                   It should unfold_untrusted_macros */
                expr decl_type  = unfold_untrusted_macros(m_env, Pi(args, mlocal_type(field.local)));
                expr val        = mk_app(m_ctx, get_id_name(), *field.default_val);
                expr decl_value = unfold_untrusted_macros(m_env, Fun(args, val));
                name_set used_univs;
                used_univs = collect_univ_params(decl_value, used_univs);
                used_univs = collect_univ_params(decl_type, used_univs);
                level_param_names decl_lvls = to_level_param_names(used_univs);
                declaration new_decl = mk_definition_inferring_trusted(m_env, decl_name, decl_lvls,
                                                                       decl_type, decl_value, reducibility_hints::mk_abbreviation());
                m_env = module::add(m_env, check(m_env, new_decl));
                m_env = set_reducible(m_env, decl_name, reducible_status::Reducible, true);
            }
        }
    }

    void add_rec_on_alias(name const & n) {
        name rec_on_name(m_name, "rec_on");
        declaration rec_on_decl = m_env.get(rec_on_name);
        declaration new_decl = mk_definition_inferring_trusted(m_env, n, rec_on_decl.get_univ_params(),
                                                               rec_on_decl.get_type(), rec_on_decl.get_value(),
                                                               reducibility_hints::mk_abbreviation());
        m_env = module::add(m_env, check(m_env, new_decl));
        m_env = set_reducible(m_env, n, reducible_status::Reducible, true);
        add_alias(n);
    }

    void declare_auxiliary() {
        m_env = mk_rec_on(m_env, m_name);
        name rec_on_name(m_name, "rec_on");
        add_rec_alias(rec_on_name);
        m_env = add_aux_recursor(m_env, rec_on_name);
        name cases_on_name(m_name, "cases_on");
        add_rec_on_alias(cases_on_name);
        m_env = add_aux_recursor(m_env, cases_on_name);
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
            expr parent_type               = m_ctx.infer(parent);
            if (!is_sort(parent_type))
                throw_ill_formed_parent(parent_name);
            level parent_rlvl              = sort_level(parent_type);
            expr st_type                   = mk_app(mk_constant(m_name, st_ls), m_params);
            binder_info bi;
            if (m_attrs.has_class())
                bi = mk_inst_implicit_binder_info();
            expr st                        = mk_local(mk_fresh_name(), "s", st_type, bi);
            expr coercion_type             = infer_implicit(Pi(m_params, Pi(st, parent, m_p), m_p), m_params.size(), true);;
            expr coercion_value            = parent_intro;
            for (unsigned idx : fmap) {
                expr const & field = m_fields[idx].local;
                name proj_name = m_name + mlocal_name(field);
                expr proj      = mk_app(mk_app(mk_constant(proj_name, st_ls), m_params), st);
                coercion_value     = mk_app(coercion_value, proj);
            }
            coercion_value                 = Fun(m_params, Fun(st, coercion_value, m_p), m_p);
            name coercion_name             = coercion_names[i];
            bool use_conv_opt              = false;
            declaration coercion_decl      = mk_definition_inferring_trusted(m_env, coercion_name, lnames,
                                                                             coercion_type, coercion_value, use_conv_opt);
            m_env = module::add(m_env, check(m_env, coercion_decl));
            m_env = set_reducible(m_env, coercion_name, reducible_status::Reducible, true);
            add_alias(coercion_name);
            m_env = vm_compile(m_env, m_env.get(coercion_name));
            if (!m_private_parents[i]) {
                if (m_attrs.has_class() && is_class(m_env, parent_name)) {
                    // if both are classes, then we also mark coercion_name as an instance
                    m_env = add_instance(m_env, coercion_name, m_prio, true);
                }
            }
        }
    }

    void declare_no_confusion() {
        if (!has_eq_decls(m_env))
            return;
        if (!has_heq_decls(m_env))
            return;
        m_env = mk_no_confusion(m_env, m_name);
        name no_confusion_name(m_name, "no_confusion");
        add_alias(no_confusion_name);
    }

    void declare_injective_lemmas() {
        if (!has_eq_decls(m_env))
            return;
        if (!has_heq_decls(m_env))
            return;
        if (!has_and_decls(m_env))
            return;
        m_env = mk_injective_lemmas(m_env, m_name);
        add_alias(mk_injective_name(m_name));
        add_alias(mk_injective_arrow_name(m_name));
    }

    void add_doc_string() {
        if (m_doc_string)
            m_env = ::lean::add_doc_string(m_env, m_name, *m_doc_string);
    }

    environment operator()() {
        process_header();
        module::scope_pos_info scope(m_name_pos);
        if (m_p.curr_is_token(get_assign_tk())) {
            m_p.check_token_next(get_assign_tk(), "invalid 'structure', ':=' expected");
            m_mk_pos = m_p.pos();
            if (m_p.curr_is_token(get_lparen_tk()) || m_p.curr_is_token(get_lcurly_tk()) ||
                m_p.curr_is_token(get_lbracket_tk())) {
                m_mk_short = LEAN_DEFAULT_STRUCTURE_INTRO;
                m_mk_infer = implicit_infer_kind::Implicit;
            } else {
                m_mk_short = m_p.check_atomic_id_next("invalid 'structure', atomic identifier expected");
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
        declare_defaults();
        declare_auxiliary();
        declare_coercions();
        add_doc_string();
        if (!m_inductive_predicate) {
            declare_no_confusion();
            declare_injective_lemmas();
        }
        return m_env;
    }
};

environment structure_cmd_ex(parser & p, decl_attributes const & attrs, decl_modifiers const & modifiers) {
    p.next();
    return structure_cmd_fn(p, attrs, modifiers)();
}

environment structure_cmd(parser & p) {
    return structure_cmd_ex(p, {}, {});
}

environment class_cmd_ex(parser & p, decl_modifiers const & modifiers) {
    decl_attributes attrs;
    attrs.set_attribute(p.env(), "class");
    p.next();
    if (p.curr_is_token(get_inductive_tk())) {
        return inductive_cmd_ex(p, attrs, modifiers.m_is_meta);
    } else {
        return structure_cmd_fn(p, attrs, modifiers)();
    }
}

environment class_cmd(parser & p) {
    return class_cmd_ex(p, {});
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

void register_structure_cmd(cmd_table & r) {
    add_cmd(r, cmd_info("structure",   "declare a new structure/record type", structure_cmd, false));
    add_cmd(r, cmd_info("class",       "declare a new class", class_cmd, false));
}
}
