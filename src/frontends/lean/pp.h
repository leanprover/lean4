/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <utility>
#include <limits>
#include "util/pair.h"
#include "util/name_map.h"
#include "util/name_set.h"
#include "util/sexpr/options.h"
#include "util/sexpr/format.h"
#include "kernel/environment.h"
#include "kernel/abstract_type_context.h"
#include "frontends/lean/token_table.h"
#include "util/numerics/mpz.h"

namespace lean {
class notation_entry;

class pretty_fn {
public:
    static unsigned max_bp() { return get_max_prec(); }
    static unsigned inf_bp() { return std::numeric_limits<unsigned>::max(); }
    /** \brief A pretty-printed format together with its left- and right-binding power
     *
     * The lbp is the binding power of its leftmost token. The invariant is that
     * for `bp < m_rbp`, `parse_expr(m_fmt, bp) == parse_expr(m_fmt, 0)`, i.e. the whole input is parsed.
     *
     * The rbp is (roughly) the binding power of its trailing parse_expr call, if any. The invariant is that
     * appending a token with binding power >= rbp should still parse no more than m_fmt.
     */
    class result {
        unsigned m_lbp;
        unsigned m_rbp;
        format   m_fmt;
    public:
        result():m_lbp(max_bp()), m_rbp(max_bp()) {}
        result(format const & fmt):m_lbp(inf_bp()), m_rbp(inf_bp()), m_fmt(fmt) {}
        result(unsigned rbp, format const & fmt):m_lbp(max_bp()), m_rbp(rbp), m_fmt(fmt) {}
        result(unsigned lbp, unsigned rbp, format const & fmt):m_lbp(lbp), m_rbp(rbp), m_fmt(fmt) {}
        unsigned lbp() const { return m_lbp; }
        unsigned rbp() const { return m_rbp; }
        format const & fmt() const { return m_fmt; }
    };
private:
    environment             m_env;
    abstract_type_context & m_ctx;
    token_table const &     m_token_table;
    unsigned                m_num_steps;
    unsigned                m_depth;
    name                    m_meta_prefix;
    unsigned                m_next_meta_idx;
    name_map<name>          m_purify_meta_table;
    name_set                m_purify_used_metas;
    name_map<name>          m_purify_local_table;
    name_set                m_purify_used_locals;
    // cached configuration
    options                 m_options;
    unsigned                m_indent;
    unsigned                m_max_depth;
    unsigned                m_max_steps;
    bool                    m_implict;          //!< if true show implicit arguments
    bool                    m_proofs;           //!< if true show proof terms
    bool                    m_unicode;          //!< if true use unicode chars
    bool                    m_coercion;         //!< if true show coercions
    bool                    m_num_nat_coe;      //!< true when !m_coercion && env has coercion from num -> nat
    bool                    m_notation;
    bool                    m_universes;
    bool                    m_full_names;
    bool                    m_private_names;
    bool                    m_purify_metavars;
    bool                    m_purify_locals;
    bool                    m_locals_full_names;
    bool                    m_beta;
    bool                    m_numerals;
    bool                    m_strings;
    bool                    m_hide_full_terms;
    bool                    m_hide_comp_irrel;
    bool                    m_preterm;
    bool                    m_binder_types;
    bool                    m_delayed_abstraction;
    bool                    m_structure_instances;
    bool                    m_structure_instances_qualifier;
    bool                    m_structure_projections;
    bool                    m_use_holes;
    bool                    m_annotations;

    name mk_metavar_name(name const & m, optional<name> const & prefix = optional<name>());
    name mk_metavar_name(name const & m, name const & prefix) {
        return mk_metavar_name(m, optional<name>(prefix));
    }
    name mk_local_name(name const & n, name const & suggested);
    level purify(level const & l);
    expr purify(expr const & e);
    bool is_implicit(expr const & f);
    bool is_default_arg_app(expr const & e);
    bool is_prop(expr const & e);
    bool has_implicit_args(expr const & f);
    optional<name> is_aliased(name const & n) const;

    format escape(name const & n);

    format pp_child(level const & l);
    format pp_max(level l);
    format pp_meta(level const & l);
    format pp_level(level const & l);

    format pp_binder(expr const & local);
    format pp_binder_block(buffer<name> const & names, expr const & type, binder_info const & bi);
    format pp_binders(buffer<expr> const & locals);

    bool match(level const & p, level const & l);
    bool match(expr const & p, expr const & e, buffer<optional<expr>> & args);
    /** \brief pretty-print e parsed with rbp, terminated by a token with lbp */
    result pp_notation_child(expr const & e, unsigned rbp, unsigned lbp);
    optional<result> pp_notation(notation_entry const & entry, buffer<optional<expr>> & args);
    optional<result> pp_notation(expr const & e);

    result add_paren_if_needed(result const & r, unsigned bp);
    std::pair<bool, token_table const *> needs_space_sep(token_table const * t, std::string const &s1, std::string const &s2) const;

    result pp_overriden_local_ref(expr const & e);
    optional<result> pp_local_ref(expr const & e);

    result pp_hide_coercion(expr const & e, unsigned bp, bool ignore_hide = false);
    result pp_hide_coercion_fn(expr const & e, unsigned bp, bool ignore_hide = false);
    result pp_child_core(expr const & e, unsigned bp, bool ignore_hide = false);
    result pp_child(expr const & e, unsigned bp, bool ignore_hide = false);
    result pp_subtype(expr const & e);
    result pp_sep(expr const & e);
    result pp_set_of(expr const & e);
    result pp_explicit_collection(buffer<expr> const & elems);
    result pp_var(expr const & e);
    result pp_sort(expr const & e);
    result pp_const(expr const & e, optional<unsigned> const & num_ref_univs = optional<unsigned>());
    result pp_meta(expr const & e);
    result pp_local(expr const & e);
    result pp_app(expr const & e);
    result pp_lambda(expr const & e);
    result pp_structure_instance(expr const & e);
    bool is_field_notation_candidate(expr const & e);
    result pp_field_notation(expr const & e);
    result pp_pi(expr const & e);
    result pp_have(expr const & e);
    result pp_show(expr const & e);
    format pp_equation(expr const & e);
    optional<result> pp_equations(expr const & e);
    result pp_macro_default(expr const & e);
    result pp_macro(expr const & e);
    result pp_explicit(expr const & e);
    result pp_delayed_abstraction(expr const & e);
    result pp_let(expr e);
    result pp_num(mpz const & n, unsigned bp);
    result pp_prod(expr const & e);
    void set_options_core(options const & o);

    expr infer_type(expr const & e);
public:
    pretty_fn(environment const & env, options const & o, abstract_type_context & ctx);
    result pp(expr const & e, bool ignore_hide = false);
    void set_options(options const & o);
    options const & get_options() const { return m_options; }
    format operator()(expr const & e);
};

formatter_factory mk_pretty_formatter_factory();
void initialize_pp();
void finalize_pp();
}
