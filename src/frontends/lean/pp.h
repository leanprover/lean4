/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <limits>
#include "util/pair.h"
#include "util/name_map.h"
#include "util/name_set.h"
#include "util/sexpr/options.h"
#include "util/sexpr/format.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "frontends/lean/token_table.h"

namespace lean {
class notation_entry;

class pretty_fn {
public:
    static unsigned max_bp() { return get_max_prec(); }
    static unsigned inf_bp() { return std::numeric_limits<unsigned>::max(); }
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
    environment         m_env;
    type_checker        m_tc;
    token_table const & m_token_table;
    unsigned            m_num_steps;
    unsigned            m_depth;
    name                m_meta_prefix;
    unsigned            m_next_meta_idx;
    name_map<name>      m_purify_meta_table;
    name_set            m_purify_used_metas;
    name_map<name>      m_purify_local_table;
    name_set            m_purify_used_locals;
    // cached configuration
    options             m_options;
    unsigned            m_indent;
    unsigned            m_max_depth;
    unsigned            m_max_steps;
    bool                m_implict;          //!< if true show implicit arguments
    bool                m_unicode;          //!< if true use unicode chars
    bool                m_coercion;         //!< if true show coercions
    bool                m_num_nat_coe;      //!< truen when !m_coercion && env has coercion from num -> nat
    bool                m_notation;
    bool                m_universes;
    bool                m_full_names;
    bool                m_private_names;
    bool                m_metavar_args;
    bool                m_purify_metavars;
    bool                m_purify_locals;
    bool                m_beta;
    bool                m_numerals;
    bool                m_abbreviations;
    bool                m_hide_full_terms;
    bool                m_extra_spaces;
    bool                m_preterm;

    name mk_metavar_name(name const & m);
    name mk_local_name(name const & n, name const & suggested);
    level purify(level const & l);
    expr purify(expr const & e);
    bool is_implicit(expr const & f);
    bool is_prop(expr const & e);
    bool has_implicit_args(expr const & f);
    optional<name> is_aliased(name const & n) const;
    optional<name> is_abbreviated(expr const & e) const;

    format pp_binder(expr const & local);
    format pp_binder_block(buffer<name> const & names, expr const & type, binder_info const & bi);
    format pp_binders(buffer<expr> const & locals);
    format pp_level(level const & l);

    bool match(level const & p, level const & l);
    bool match(expr const & p, expr const & e, buffer<optional<expr>> & args);
    result pp_notation_child(expr const & e, unsigned lbp, unsigned rbp);
    optional<result> pp_notation(notation_entry const & entry, buffer<optional<expr>> & args);
    optional<result> pp_notation(expr const & e);

    result add_paren_if_needed(result const & r, unsigned bp);
    std::pair<bool, token_table const *> needs_space_sep(token_table const * t, std::string const &s1, std::string const &s2) const;

    result pp_overriden_local_ref(expr const & e);
    bool ignore_local_ref(expr const & e);
    optional<result> pp_local_ref(expr const & e);

    result pp_coercion_fn(expr const & e, unsigned sz, bool ignore_hide = false);
    result pp_coercion(expr const & e, unsigned bp, bool ignore_hide = false);
    result pp_child_core(expr const & e, unsigned bp, bool ignore_hide = false);
    result pp_child(expr const & e, unsigned bp, bool ignore_hide = false);
    result pp_var(expr const & e);
    result pp_sort(expr const & e);
    result pp_const(expr const & e, optional<unsigned> const & num_ref_univs = optional<unsigned>());
    result pp_meta(expr const & e);
    result pp_local(expr const & e);
    result pp_app(expr const & e);
    result pp_lambda(expr const & e);
    result pp_pi(expr const & e);
    result pp_have(expr const & e);
    result pp_show(expr const & e);
    result pp_macro(expr const & e);
    result pp_explicit(expr const & e);
    result pp_let(expr e);
    result pp_num(mpz const & n);
    // If fn is true, then \c e is of the form (f a), and the abbreviation is \c f.
    result pp_abbreviation(expr const & e, name const & abbrev, bool fn, unsigned bp = 0, bool ignore_hide = false);
    void set_options_core(options const & o);

public:
    pretty_fn(environment const & env, options const & o);
    result pp(expr const & e, bool ignore_hide = false);
    void set_options(options const & o);
    options const & get_options() const { return m_options; }
    format operator()(expr const & e);
};

formatter_factory mk_pretty_formatter_factory();
void initialize_pp();
void finalize_pp();
}
