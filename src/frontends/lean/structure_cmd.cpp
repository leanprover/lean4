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
#include <library/replace_visitor.h>
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
#include "library/constructions/drec.h"
#include "library/equations_compiler/util.h"
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
#include "frontends/lean/structure_cmd.h"

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

// We mark subobject fields by prefixing them with "_" in the structure's intro rule
bool is_internal_subobject_field(name const & field_name) {
    return field_name.is_string() && strncmp(field_name.get_string(), "_", 1) == 0;
}

name deinternalize_field_name(name const & fname) {
    if (is_internal_subobject_field(fname))
        return std::string(fname.get_string()).substr(1);
    return fname;
}

name mk_internal_subobject_field_name(name const & fname) {
    return fname.append_before("_");
}

buffer<name> get_structure_fields(environment const & env, name const & S) {
    lean_assert(is_structure_like(env, S));
    buffer<name> fields;
    level_param_names ls; unsigned nparams; inductive::intro_rule intro;
    std::tie(ls, nparams, intro) = get_structure_info(env, S);
    expr intro_type = inductive::intro_rule_type(intro);
    unsigned i = 0;
    while (is_pi(intro_type)) {
        if (i >= nparams)
            fields.push_back(deinternalize_field_name(binding_name(intro_type)));
        i++;
        intro_type = binding_body(intro_type);
    }
    return fields;
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
    name field_name = S + deinternalize_field_name(binding_name(intro_type));
    return get_projection_info(env, field_name) != nullptr;
}

optional<name> is_subobject_field(environment const & env, name const & S_name, name const & fname) {
    expr intro_type = inductive::intro_rule_type(std::get<2>(get_structure_info(env, S_name)));
    auto n = mk_internal_subobject_field_name(fname);
    while (is_pi(intro_type)) {
        if (binding_name(intro_type) == n)
            return some(const_name(get_app_fn(binding_domain(intro_type))));
        intro_type = binding_body(intro_type);
    }
    return {};
}

buffer<name> get_parent_structures(environment const & env, name const & S_name) {
    buffer<name> parents;
    for (name const & field_name : get_structure_fields(env, S_name)) {
        if (auto p = is_subobject_field(env, S_name, field_name))
            parents.push_back(*p);
    }
    return parents;
}

name_set get_ancestor_structures(environment const & env, name const & S_name) {
    name_set ns;
    std::function<void(name const &)> go = [&](name const & n) {
        for (auto const & p : get_parent_structures(env, n)) {
            if (!ns.contains(p)) {
                ns.insert(p);
                go(p);
            }
        }
    };
    go(S_name);
    return ns;
}

optional<name> find_field(environment const & env, name const & S_name, name const & fname) {
    for (auto const & n : get_structure_fields(env, S_name))
        if (n == fname)
            return some(S_name);
    for (auto const & p : get_parent_structures(env, S_name)) {
        if (auto n = find_field(env, p, fname))
            return n;
    }
    return {};
}

void get_structure_fields_flattened(environment const & env, name const & structure_name, buffer<name> & full_fnames) {
    for (auto const & fname : get_structure_fields(env, structure_name)) {
        full_fnames.push_back(structure_name + fname);
        if (auto p = is_subobject_field(env, structure_name, fname))
            get_structure_fields_flattened(env, *p, full_fnames);
    }
}

expr mk_proj_app(environment const & env, name const & S_name, name const & fname, expr const & e, expr const & ref) {
    if (is_structure_like(env, S_name)) {
        name proj_name = S_name + fname;
        if (get_projection_info(env, proj_name)) {
            auto proj    = mk_explicit(copy_tag(ref, mk_constant(proj_name)));
            auto nparams = std::get<1>(get_structure_info(env, S_name));
            for (unsigned i = 0; i < nparams; i++)
                proj = mk_app(proj, mk_expr_placeholder());
            return mk_app(proj, e);
        }
    }
    return mk_app(copy_tag(ref, mk_constant(S_name + fname)), e);
}

optional<expr> mk_base_projections(environment const & env, name const & S_name, name const & base_S_name, expr const & e) {
    if (S_name == base_S_name)
        return some_expr(e);
    for (name const & fname : get_structure_fields(env, S_name)) {
        if (auto p = is_subobject_field(env, S_name, fname)) {
            auto projs = mk_proj_app(env, S_name, fname, e, {});
            if (auto r = mk_base_projections(env, *p, base_S_name, projs))
                return r;
        }
    }
    return {};
}

optional<name> has_default_value(environment const & env, name const & S_name, name const & fname) {
    name default_name(S_name + fname, "_default");
    if (env.find(default_name))
        return optional<name>(default_name);
    for (auto const & p : get_parent_structures(env, S_name)) {
        if (auto n = has_default_value(env, p, fname))
            return n;
    }
    return optional<name>();
}

expr mk_field_default_value(environment const & env, name const & full_field_name, std::function<expr(name const &)> const & get_field_value) {
    optional<name> default_name = has_default_value(env, full_field_name.get_prefix(), full_field_name.get_string());
    lean_assert(default_name);
    declaration decl = env.get(*default_name);
    expr value = decl.get_value();
    buffer<expr> args;
    while (is_lambda(value)) {
        if (is_explicit(binding_info(value))) {
            name fname = binding_name(value);
            args.push_back(get_field_value(fname));
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
    enum class field_kind { new_field, from_parent, subobject };
    struct field_decl {
        expr                m_local; // name, type, and pos as an expr::local
        optional<expr>      m_default_val;
        field_kind          m_kind;
        implicit_infer_kind m_infer_kind;
        bool                m_has_new_default; // if true, (re-)declare default value in this structure

        field_decl(expr const & local, optional<expr> const & default_val, field_kind kind,
                   implicit_infer_kind infer_kind = implicit_infer_kind::Implicit):
                m_local(local), m_default_val(default_val), m_kind(kind), m_infer_kind(infer_kind),
                m_has_new_default(default_val && kind == field_kind::new_field) {}

        name const & get_name() const { return mlocal_name(m_local); }
        expr const & get_type() const { return mlocal_type(m_local); }
    };

    parser &                    m_p;
    cmd_meta                    m_meta_info;
    environment                 m_env;
    type_context_old                m_ctx;
    name                        m_namespace;
    name                        m_name;
    name                        m_given_name;
    pos_info                    m_name_pos;
    buffer<name>                m_level_names;
    buffer<expr>                m_params;
    expr                        m_type;
    buffer<optional<name>>      m_parent_refs;
    buffer<expr>                m_parents;
    buffer<bool>                m_private_parents;
    name                        m_mk;
    name                        m_mk_short;
    name                        m_private_prefix;
    pos_info                    m_mk_pos;
    implicit_infer_kind         m_mk_infer;
    buffer<field_decl>          m_fields;
    std::vector<rename_vector>  m_renames;
    std::vector<field_map>      m_field_maps;
    bool                        m_explicit_universe_params;
    bool                        m_infer_result_universe;
    bool                        m_inductive_predicate;
    bool                        m_subobjects;
    levels                      m_ctx_levels; // context levels for creating aliases
    buffer<expr>                m_ctx_locals; // context local constants for creating aliases
    unsigned                    m_prio;

    structure_cmd_fn(parser & p, cmd_meta const & meta):
        m_p(p),
        m_meta_info(meta),
        m_env(p.env()),
        m_ctx(p.env()),
        m_namespace(get_namespace(m_env)) {
        m_explicit_universe_params = false;
        m_infer_result_universe    = false;
        m_inductive_predicate      = false;
        m_subobjects               = !p.get_options().get_bool("old_structure_cmd", false);
        m_prio                     = get_default_priority(p.get_options());
        if (!meta.m_attrs.ok_for_inductive_type())
            throw exception("only attribute [class] accepted for structures");
    }

    bool is_private() const { return m_meta_info.m_modifiers.m_is_private; }

    /** \brief Parse structure name and (optional) universe parameters */
    void parse_decl_name() {
        m_name_pos = m_p.pos();
        buffer<name> ls_buffer;
        if (parse_univ_params(m_p, ls_buffer)) {
            m_explicit_universe_params = true;
            m_level_names.append(ls_buffer);
        } else {
            m_explicit_universe_params = false;
        }
        m_given_name = m_p.check_decl_id_next("invalid 'structure', identifier expected");
        if (is_private()) {
            std::tie(m_env, m_private_prefix) = mk_private_prefix(m_env);
            m_name = m_private_prefix + m_given_name;
            m_env  = register_private_name(m_env, m_given_name, m_name);
        } else {
            m_name = m_namespace + m_given_name;
        }
    }

    /** \brief Parse structure parameters */
    void parse_params() {
        if (!m_p.curr_is_token(get_extends_tk()) && !m_p.curr_is_token(get_assign_tk()) &&
            !m_p.curr_is_token(get_colon_tk())) {
            unsigned rbp = 0;
            bool allow_default = true;
            m_p.parse_binders(m_params, rbp, allow_default);
        }
        for (expr const & l : m_params)
            m_p.add_local(l);
    }

    /** \brief Check whether \c parent is really an inductive datatype declaration that can be viewed as a "record".
        That is, it is not part of a mutually recursive declaration, it has only one constructor,
        and it does not have indices.
        Returns the structure's name if successful.
    */
    name const & check_parent(expr const & parent) {
        expr fn = get_app_fn(parent);
        if (m_subobjects && is_local_ref(fn))
            fn = get_explicit_arg(get_app_fn(get_as_atomic_arg(fn)));
        if (!is_constant(fn))
            throw elaborator_exception(parent, "invalid 'structure', expression must be a 'parent' structure");
        name const & S = const_name(fn);
        if (!is_structure_like(m_env, S))
            throw elaborator_exception(parent, sstream() << "invalid 'structure' extends, '" << S << "' is not a structure");
        return S;
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
                name const & parent_name = check_parent(parent);
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
                if (!m_subobjects && m_p.curr_is_token(get_renaming_tk())) {
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

    /* We elaborate the structure header and fields by constructing, elaborating, and destructing a single big
     * telescope expression that contains all relevant expression in their correct respective contexts. For example, for
     *
     *   parameter A : Type
     *   structure s (B : Type) extends s' A B : Type := ...
     *
     *  `elaborate_header` will build the telescope `Pi (A : Type) (B : Type), s' A B -> Type`. */

    using tele_elab = std::function<expr(expr)>;

    // `elaborate_for_each(buf, tmp, f, elab)` maps to
    // `f(buf[buf.size()-1], buf.size()-1, tmp, f(buf[buf.size()-2], buf.size()-2, tmp, ... f(buf[0], 0, tmp, elab(tmp)) ...))`
    template <class T>
    expr elaborate_for_each(buffer<T> & buf, expr const & tmp, std::function<expr(T &, unsigned, expr const &, tele_elab)> f,
                            tele_elab elab, unsigned i = 0) {
        if (i == buf.size())
            return elab(tmp);
        elab = [&, elab](expr const & tmp) {
            return elaborate_for_each(buf, tmp, f, elab, i + 1);
        };
        unsigned idx = buf.size() - 1 - i;
        return f(buf[idx], idx, tmp, elab);
    }

    expr elaborate_parent(bool in_header, expr & parent, unsigned i, expr const & tmp, tele_elab elab) {
        if (!in_header && m_subobjects) {
            return elab(tmp);
        } else {
            expr new_tmp = elab(mk_arrow(in_header ? parent : mk_as_is(parent), tmp));
            parent       = copy_tag(parent, expr(binding_domain(new_tmp)));

            if (m_subobjects) {
                // immediately register parent field so that we can use it in `mk_parent_expr` below
                name const & parent_name = check_parent(parent);
                name fname;
                if (auto const & ref = m_parent_refs[i])
                    fname = *ref;
                else
                    fname = name(parent_name.get_string()).append_before("to_");
                binder_info bi;
                if (m_meta_info.m_attrs.has_class() && is_class(m_env, parent_name))
                    // make superclass fields inst implicit
                    bi = mk_inst_implicit_binder_info();
                expr field = mk_local(fname, mk_as_is(parent), bi);
                m_fields.emplace_back(field, none_expr(), field_kind::subobject);
            }

            new_tmp      = binding_body(new_tmp);
            if (!in_header || m_subobjects) {
                new_tmp = instantiate(new_tmp, mk_parent_expr(i));
            }
            return new_tmp;
        }
    }

    expr elaborate_local(bool as_is, expr & local, unsigned, expr const & tmp, tele_elab elab) {
        expr new_tmp   = elab(as_is ? Pi_as_is(local, tmp) : Pi(local, tmp));
        expr new_local = update_mlocal(local, binding_domain(new_tmp));
        local          = new_local;
        return instantiate(binding_body(new_tmp), new_local);
    }

    /** \brief elaborate parameters and "parent" types */
    void elaborate_header() {
        auto _ = m_p.no_error_recovery_scope(); // we require that m_p.elaborate_type(mk_let()) is a let, etc.

        using namespace std::placeholders; // NOLINT
        // NB: telescope is built inside-out, i.e. ctx -> params -> parents -> type
        expr tmp = m_type;
        m_type = elaborate_for_each<expr>(m_parents, tmp, std::bind(&structure_cmd_fn::elaborate_parent, this, true, _1, _2, _3, _4), [&](expr tmp) {
            return elaborate_for_each<expr>(m_params, tmp, std::bind(&structure_cmd_fn::elaborate_local, this, false, _1, _2, _3, _4), [&](expr tmp) {
                buffer<name> lp_names;
                buffer<expr> ctx;
                collect_implicit_locals(m_p, lp_names, ctx, tmp);
                return elaborate_for_each<expr>(ctx, tmp, std::bind(&structure_cmd_fn::elaborate_local, this, true, _1, _2, _3, _4), [&](expr tmp) {
                    level_param_names new_ls;
                    expr new_tmp;
                    std::tie(new_tmp, new_ls) = m_p.elaborate_type(m_name, list<expr>(), tmp);
                    levels new_meta_ls = map2<level>(new_ls, [&](name const &) { return m_ctx.mk_univ_metavar_decl(); });
                    return instantiate_univ_params(new_tmp, new_ls, new_meta_ls);
                });
            });
        });
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
            if (m_fields[i].get_name() == fname) {
                if (m_ctx.is_def_eq(m_fields[i].get_type(), ftype)) {
                    return optional<unsigned>(i);
                } else {
                    expr prev_ftype = m_fields[i].get_type();
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

    field_decl * get_field_by_name(name const & name) {
        auto it = std::find_if(m_fields.begin(), m_fields.end(), [&](field_decl const & field) {
            return field.get_name() == name;
        });
        return it != m_fields.end() ? it : nullptr;
    }

    expr mk_field_default_value(name const & full_field_name) {
        return ::lean::mk_field_default_value(m_env, full_field_name, [&](name const & fname) {
                return mk_explicit(get_field_by_name(fname)->m_local);
            });
    }

    /** \brief Process extends clauses.
        This method also populates the vector m_field_maps and m_fields. */
    void process_extends() {
        // We have already pushed subobjects in `elaborate_parent`
        lean_assert(m_fields.size() == (m_subobjects ? m_parents.size() : 0));
        lean_assert(m_field_maps.empty());

        for (unsigned i = 0; i < m_parents.size(); i++) {
            expr const & parent = m_parents[i];
            name const & parent_name = check_parent(parent);
            rename_vector const & renames = m_renames[i];
            m_field_maps.push_back(field_map());
            field_map & fmap = m_field_maps.back();
            buffer<expr> args;
            expr parent_fn = get_app_args(parent, args);
            if (m_subobjects) {
                buffer<name> subfield_names;
                get_structure_fields_flattened(m_env, parent_name, subfield_names);
                // register inherited fields via projections of the subobject field
                for (name const & full_fname : subfield_names) {
                    name base_S_name = full_fname.get_prefix();
                    name fname = full_fname.get_string();
                    for (auto const & field : m_fields) {
                        if (field.get_name() == fname) {
                            throw elaborator_exception(
                                    parent, sstream() << "invalid 'structure' header, field '" << fname
                                                      << "' from '" << parent_name
                                                      << "' has already been declared");
                        }
                    }

                    // Given parameter types `Ps` of `base_S_name`, the projection `full_fname` has
                    // type `Pi (ps : Ps) (x : base_S_name ps), A` for some `A`. We don't know `ps`, but we can obtain `x`
                    // by projecting our new subobject field and then obtain `A` as
                    // `(fun {ps : Ps} (x : base_S_name ps), A) x`.
                    auto base_obj_opt = mk_base_projections(m_env, parent_name, base_S_name, m_fields[i].m_local);
                    if (!base_obj_opt) {
                        throw elaborator_exception(parent, "cannot make base projection");
                    }
                    expr base_obj = *base_obj_opt;
                    level_param_names lparams; unsigned nparams; inductive::intro_rule intro;
                    std::tie(lparams, nparams, intro) = get_parent_info(base_S_name);
                    levels meta_ls = map2<level>(lparams, [&](name const &) { return m_ctx.mk_univ_metavar_decl(); });
                    expr type = instantiate_univ_params(m_p.env().get(full_fname).get_type(), lparams, meta_ls);
                    std::function<expr(expr const &, unsigned)> pi_to_lam = [&](expr const & e, unsigned i) {
                        if (i == nparams + 1)
                            return mk_as_is(e);
                        return mk_lambda(binding_name(e), mk_as_is(binding_domain(e)), pi_to_lam(binding_body(e), i + 1),
                                         i < nparams ? mk_implicit_binder_info() : binder_info());
                    };
                    type = pi_to_lam(type, 0);
                    type = mk_app(type, base_obj);

                    expr proj = mk_proj_app(m_env, full_fname.get_prefix(), full_fname.get_string(), base_obj);
                    expr subfield = mk_local(full_fname.get_string(), type);
                    m_fields.emplace_back(subfield, some_expr(proj), field_kind::from_parent);
                }
            } else {
                level_param_names lparams; unsigned nparams; inductive::intro_rule intro;
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
                        field = m_fields[*fidx].m_local;
                        if (local_info(field) != binding_info(intro_type)) {
                            throw elaborator_exception(parent,
                                                       sstream() << "invalid 'structure' header, field '" << fname <<
                                                       "' has already been declared with a different binder annotation");
                        }
                    } else {
                        field = mk_local(fname, mk_as_is(ftype), binding_info(intro_type));
                        fmap.push_back(m_fields.size());
                        m_fields.emplace_back(field, none_expr(), field_kind::from_parent);
                    }
                    intro_type = instantiate(binding_body(intro_type), field);
                }
                // construct and add default values now that all fields have been defined
                for (size_t fmap_idx = fmap_start; fmap_idx < fmap.size(); fmap_idx++) {
                    field_decl & field = m_fields[fmap[fmap_start]];
                    name fname = field.get_name();
                    name full_fname = parent_name + fname;
                    if (optional<name> fdefault_name = has_default_value(m_env, parent_name, fname)) {
                        expr fdefault = mk_field_default_value(full_fname);
                        if (!field.m_default_val) {
                            field.m_default_val = fdefault;
                        }
                        // TODO(gabriel): the defeq check below is completely broken because it compares pre-expressions
                        /*
                        } else if (field.m_default_val && !m_ctx.is_def_eq(*field.m_default_val, fdefault)) {
                            expr prev_default = *field.m_default_val;
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
                        */
                    }
                    fmap_start++;
                }
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
            decl.m_local  = m_ctx.instantiate_mvars(decl.m_local);
            if (decl.m_default_val)
                decl.m_default_val = m_ctx.instantiate_mvars(*decl.m_default_val);
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
        if (m_subobjects)
            return m_fields[i].m_local;
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
            expr const & field = m_fields[idx].m_local;
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
            m_p.add_local(decl.m_local);
        if (!m_subobjects) {
            for (unsigned i = 0; i < m_parents.size(); i++) {
                if (auto n = m_parent_refs[i])
                    m_p.add_local_expr(*n, mk_as_is(mk_parent_expr(i)));
            }
        }
    }

    void parse_field_block(binder_info const & bi) {
        buffer<pair<pos_info, name>> names;
        auto start_pos = m_p.pos();
        while (m_p.curr_is_identifier()) {
            auto p = m_p.pos();
            auto n = m_p.check_atomic_id_next("invalid field, atomic identifier expected");
            if (is_internal_subobject_field(n))
                throw parser_error(sstream() << "invalid field name '" << n << "', identifiers starting with '_' are reserved to the system", p);
            names.emplace_back(p, n);
        }
        if (names.empty())
            throw parser_error("invalid field, identifier expected", m_p.pos());

        expr type;
        optional<expr> default_value;
        implicit_infer_kind kind = implicit_infer_kind::Implicit;
        {
            parser::local_scope scope(m_p);
            buffer<expr> params;
            if (names.size() == 1) {
                m_p.parse_optional_binders(params, kind);
                for (expr const & param : params)
                    m_p.add_local(param);
            }

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
            type = Pi(params, type);
            if (default_value)
                *default_value = Fun(params, *default_value);
        }

        if (default_value && !is_explicit(bi)) {
            throw parser_error("invalid field, it is not explicit, but it has a default value", start_pos);
        }
        for (auto p : names) {
            if (auto old_field = get_field_by_name(p.second)) {
                if (default_value && is_placeholder(type)) {
                    if (m_subobjects) {
                        expr local = mk_local(p.second, old_field->get_type(), bi);
                        field_decl field(local, default_value, field_kind::from_parent);
                        field.m_has_new_default = true;
                        m_fields.push_back(field);
                    } else {
                        old_field->m_default_val = default_value;
                        old_field->m_has_new_default = true;
                    }
                } else {
                    sstream msg;
                    msg << "field '" << p.second;
                    if (old_field->m_kind == field_kind::from_parent)
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
                m_fields.emplace_back(local, default_value, field_kind::new_field, kind);
            }
        }
    }

    /** \brief Parse new fields declared in this structure */
    void parse_new_fields() {
        parser::local_scope scope(m_p);
        add_locals();
        while (!m_p.curr_is_command_like()) {
            if (auto bi = m_p.parse_optional_binder_info()) {
                if (!m_p.parse_local_notation_decl())
                    parse_field_block(*bi);
                m_p.parse_close_binder_info(*bi);
            } else {
                break;
            }
        }
    }

    /* Elaborate `Pi n : T, tmp` for each field, or `let n : T := d in tmp` for each defaulted field that will not be
     * handled by `elaborate_new_typed_default` */
    expr elaborate_field(field_decl & decl, unsigned, expr const & tmp, tele_elab elab) {
        expr new_tmp;
        expr type  = decl.get_type();
        auto const & value = decl.m_default_val;
        if (value && (!decl.m_has_new_default || is_placeholder(decl.get_type()))) {
            new_tmp = elab(mk_let(decl.get_name(), type, *value, abstract_local(tmp, decl.m_local)));
            decl.m_local = update_mlocal(decl.m_local, let_type(new_tmp));
            decl.m_default_val = let_value(new_tmp);
            new_tmp = instantiate(let_body(new_tmp), m_subobjects ? let_value(new_tmp) : decl.m_local);
        } else if (!value || decl.m_kind == field_kind::new_field) {
            new_tmp = elab(Pi(decl.m_local, tmp));
            decl.m_local = update_mlocal(decl.m_local, binding_domain(new_tmp));
            new_tmp = instantiate(binding_body(new_tmp), decl.m_local);
        } else {
            new_tmp = elab(tmp);
        }
        return new_tmp;
    }

    /* let-elaborate new default values of fields with explicit types so that they can refer to any field, even cyclically.
     *
     *   class Eq (α : Type) :=
     *   (eq : α → α → Prop := λ a b, ¬ne a b)
     *   (ne : α → α → Prop := λ a b, ¬eq a b)
     *
     * will be elaborated as
     *
     *   Π (α : Type) (eq : α → α → Prop) (ne : α → α → Prop),
     *   let _fresh1 : α → α → Prop := ¬ne a b in
     *   let _fresh2 : α → α → Prop := ¬eq a b in
     *   Prop
     */
    expr elaborate_new_typed_default(field_decl & decl, unsigned, expr const & tmp, tele_elab elab) {
        if (!decl.m_has_new_default || is_placeholder(decl.get_type()))
            return elab(tmp);
        expr type  = decl.get_type();
        expr value = *decl.m_default_val;
        expr new_tmp = elab(mk_let(m_p.next_name(), type, value, tmp));
        decl.m_local = update_local(decl.m_local, let_type(new_tmp), local_info(decl.m_local));
        decl.m_default_val = let_value(new_tmp);
        return let_body(new_tmp);
    }

    /** \brief Elaborate new fields */
    void elaborate_new_fields() {
        auto _ = m_p.no_error_recovery_scope(); // we require that m_p.elaborate_type(mk_let()) is a let, etc.

        using namespace std::placeholders; // NOLINT
        // NB: telescope is built inside-out, i.e. params -> parents -> fields -> typed defaults -> Prop
        expr tmp = mk_Prop();
        expr new_tmp = elaborate_for_each<field_decl>(m_fields, tmp, std::bind(&structure_cmd_fn::elaborate_new_typed_default, this, _1, _2, _3, _4), [&](expr tmp) {
            return elaborate_for_each<field_decl>(m_fields, tmp, std::bind(&structure_cmd_fn::elaborate_field, this, _1, _2, _3, _4), [&](expr tmp) {
                return elaborate_for_each<expr>(m_parents, tmp, std::bind(&structure_cmd_fn::elaborate_parent, this, false, _1, _2, _3, _4), [&](expr tmp) {
                    return elaborate_for_each<expr>(m_params, tmp, std::bind(&structure_cmd_fn::elaborate_local, this, true, _1, _2, _3, _4), [&](expr tmp) {
                        collect_implicit_locals(m_p, m_level_names, m_ctx_locals, tmp);
                        return elaborate_for_each<expr>(m_ctx_locals, tmp, std::bind(&structure_cmd_fn::elaborate_local, this, true, _1, _2, _3, _4), [&](expr tmp) {
                            level_param_names new_ls;
                            expr new_tmp;
                            metavar_context mctx = m_ctx.mctx();
                            std::tie(new_tmp, new_ls) = m_p.elaborate_type(m_name, mctx, tmp);
                            m_ctx.set_mctx(mctx);
                            for (auto new_l : new_ls)
                                m_level_names.push_back(new_l);
                            return new_tmp;
                        });
                    });
                });
            });
        });
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
            level l = get_level(m_ctx, decl.get_type());
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
            out << ">> " << decl.get_name() << " : " << decl.get_type();
            if (decl.m_default_val)
                out << " := " << *decl.m_default_val;
            out << "\n";
        }
    }

    /** \brief Add context locals as extra parameters */
    void add_ctx_locals() {
        buffer<expr> params;
        params.append(m_params);
        m_params.clear();
        m_params.append(m_ctx_locals);
        m_params.append(params);
    }

    expr mk_structure_type() {
        return Pi(m_params, m_type, m_p);
    }

    expr mk_structure_type_no_params() {
        return m_type;
    }

    expr mk_intro_type_no_params() {
        levels ls = param_names_to_levels(to_list(m_level_names.begin(), m_level_names.end()));
        expr r    = mk_app(mk_constant(m_name, ls), m_params);
        for (unsigned i = 0; i < m_fields.size(); i++) {
            auto const & decl = m_fields[m_fields.size() - 1 - i];
            if (decl.m_kind != field_kind::from_parent || !m_subobjects) {
                r = abstract_local(r, decl.m_local);
                name n = decl.get_name();
                if (decl.m_kind == field_kind::subobject)
                    n = mk_internal_subobject_field_name(n);
                r = mk_pi(n, decl.get_type(), r, local_info(decl.m_local));
            }
        }
        return r;
    }

    expr mk_intro_type() {
        expr r = Pi(m_params, mk_intro_type_no_params(), m_p);
        r      = infer_implicit_params(r, m_params.size(), m_mk_infer);
        return unfold_untrusted_macros(m_env, r);
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
        if (is_private()) {
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
        bool is_trusted = !m_meta_info.m_modifiers.m_is_meta;
        m_env = module::add_inductive(m_env, decl, is_trusted);
        name rec_name = inductive::get_elim_name(m_name);
        m_env = add_namespace(m_env, m_name);
        m_env = add_protected(m_env, rec_name);
        add_alias(m_given_name, m_name);
        add_alias(m_mk);
        add_rec_alias(rec_name);
        m_env = add_structure_declaration_aux(m_env, m_p.get_options(), m_level_names, m_params,
                                              mk_local(m_name, mk_structure_type_no_params()),
                                              mk_local(m_mk, mk_intro_type_no_params()), is_trusted);
    }

    void declare_projections() {
        buffer<name> proj_names;
        buffer<implicit_infer_kind> infer_kinds;
        for (field_decl const & field : m_fields) {
            if (!m_subobjects || field.m_kind != field_kind::from_parent) {
                proj_names.push_back(m_name + mlocal_name(field.m_local));
                infer_kinds.push_back(
                        field.m_infer_kind != implicit_infer_kind::Implicit ? field.m_infer_kind : m_mk_infer);
            }
        }
        m_env = mk_projections(m_env, m_name, proj_names, infer_kinds, m_meta_info.m_attrs.has_class());
        for (auto const & n : proj_names)
            add_alias(n);
    }

    bool is_param(expr const & local) {
        for (auto const & param : m_params) {
            if (mlocal_name(param) == mlocal_name(local))
                return true;
        }
        return false;
    }

    void declare_defaults() {
        for (field_decl const & field : m_fields) {
            if (field.m_has_new_default || (!m_subobjects && field.m_default_val)) {
                expr val = *field.m_default_val;
                expr type = field.get_type();
                collected_locals used_locals;
                collect_locals(type, used_locals);
                collect_locals(val, used_locals);
                buffer<expr> args;
                // note: `mk_field_default_value` expects params to be implicit
                // and fields to be explicit
                /* Copy params first */
                for (expr const & local : used_locals.get_collected()) {
                    if (is_param(local)) {
                        if (is_explicit(local_info(local)))
                            args.push_back(update_local(local, mk_implicit_binder_info()));
                        else
                            args.push_back(local);
                    }
                }
                /* Copy fields it depends on */
                for (expr const & local : used_locals.get_collected()) {
                    if (!is_param(local))
                        args.push_back(update_local(local, binder_info()));
                }
                name decl_name  = name(m_name + field.get_name(), "_default");
                name decl_prv_name;
                if (is_private()) {
                    decl_prv_name = name(m_private_prefix + m_given_name + field.get_name(), "_default");
                } else {
                    decl_prv_name = decl_name;
                }
                /* TODO(Leo): add helper function for adding definition.
                   It should unfold_untrusted_macros */
                expr decl_type  = unfold_untrusted_macros(m_env, Pi(args, type));
                val             = mk_app(m_ctx, get_id_name(), val);
                expr decl_value = unfold_untrusted_macros(m_env, Fun(args, val));
                name_set used_univs;
                used_univs = collect_univ_params(decl_value, used_univs);
                used_univs = collect_univ_params(decl_type, used_univs);
                level_param_names decl_lvls = to_level_param_names(used_univs);
                declaration new_decl = mk_definition_inferring_trusted(m_env, decl_name, decl_lvls,
                                                                       decl_type, decl_value, reducibility_hints::mk_abbreviation());
                m_env = module::add(m_env, check(m_env, new_decl));
                if (!m_meta_info.m_modifiers.m_is_meta)
                    m_env = mk_simple_equation_lemma_for(m_env, m_p.get_options(), is_private(), decl_name, decl_prv_name, args.size());
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
        if (is_inductive_predicate(m_env, m_name))
            m_env = mk_drec(m_env, m_name);
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
            buffer<expr> parent_params;
            expr const & parent_fn         = get_app_args(parent, parent_params);
            levels const & parent_ls       = const_levels(parent_fn);
            name const & parent_name       = const_name(parent_fn);
            if (m_subobjects) {
                if (!m_private_parents[i]) {
                    if (m_meta_info.m_attrs.has_class() && is_class(m_env, parent_name)) {
                        // if both are classes, then we also mark coercion_name as an instance
                        m_env = add_instance(m_env, m_name + m_fields[i].get_name(), m_prio, true);
                    }
                }
                continue;
            }

            field_map const & fmap         = m_field_maps[i];
            auto parent_info               = get_parent_info(parent_name);
            name const & parent_intro_name = inductive::intro_rule_name(std::get<2>(parent_info));
            expr parent_intro              = mk_app(mk_constant(parent_intro_name, parent_ls), parent_params);
            expr parent_type               = m_ctx.infer(parent);
            if (!is_sort(parent_type))
                throw_ill_formed_parent(parent_name);
            level parent_rlvl              = sort_level(parent_type);
            expr st_type                   = mk_app(mk_constant(m_name, st_ls), m_params);
            binder_info bi;
            if (m_meta_info.m_attrs.has_class())
                bi = mk_inst_implicit_binder_info();
            expr st                        = mk_local(m_p.next_name(), "s", st_type, bi);
            expr coercion_type             = infer_implicit(Pi(m_params, Pi(st, parent, m_p), m_p), m_params.size(), true);;
            expr coercion_value            = parent_intro;
            for (unsigned idx : fmap) {
                name proj_name = m_name + m_fields[idx].get_name();
                expr proj      = mk_app(mk_app(mk_constant(proj_name, st_ls), m_params), st);
                coercion_value     = mk_app(coercion_value, proj);
            }
            coercion_value                 = Fun(m_params, Fun(st, coercion_value, m_p), m_p);
            name coercion_name             = coercion_names[i];
            bool use_conv_opt              = false;
            declaration coercion_decl      = mk_definition_inferring_trusted(m_env, coercion_name, lnames,
                                                                             coercion_type, coercion_value, use_conv_opt);
            m_env = module::add(m_env, check(m_env, coercion_decl));
            add_alias(coercion_name);
            m_env = vm_compile(m_env, m_env.get(coercion_name));
            if (!m_private_parents[i]) {
                if (m_meta_info.m_attrs.has_class() && is_class(m_env, parent_name)) {
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
        /* We do not generate `*.inj_eq` lemmas for classes since they can be quite expensive to
           generate for big classes, and they don't seem to be useful in this case. */
        bool gen_inj_eq = !m_meta_info.m_attrs.has_class();
        m_env = mk_injective_lemmas(m_env, m_name, gen_inj_eq);
        add_alias(mk_injective_name(m_name));
        add_alias(mk_injective_arrow_name(m_name));
    }

    void add_doc_string() {
        if (m_meta_info.m_doc_string)
            m_env = ::lean::add_doc_string(m_env, m_name, *m_meta_info.m_doc_string);
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
        add_ctx_locals();
        remove_local_vars(m_p, m_ctx_locals);
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
        /* Apply attributes last so that they may access any information on the new decl */
        m_env = m_meta_info.m_attrs.apply(m_env, m_p.ios(), m_name);
        return m_env;
    }
};

environment structure_cmd(parser & p, cmd_meta const & meta) {
    p.next();
    return structure_cmd_fn(p, meta)();
}

environment class_cmd(parser & p, cmd_meta const & _meta) {
    auto meta = _meta;
    meta.m_attrs.set_persistent(true);
    meta.m_attrs.set_attribute(p.env(), "class");
    p.next();
    if (p.curr_is_token(get_inductive_tk())) {
        return inductive_cmd(p, meta);
    } else {
        return structure_cmd_fn(p, meta)();
    }
}

void register_structure_cmd(cmd_table & r) {
    add_cmd(r, cmd_info("structure",   "declare a new structure/record type", structure_cmd, false));
    add_cmd(r, cmd_info("class",       "declare a new class", class_cmd, false));
    register_bool_option("old_structure_cmd", false, "use old structures compilation strategy");
}
}
