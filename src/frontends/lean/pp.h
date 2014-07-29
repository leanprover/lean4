/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <limits>
#include "util/name_map.h"
#include "util/name_set.h"
#include "util/sexpr/options.h"
#include "util/sexpr/format.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"

namespace lean {
class pretty_fn {
public:
    typedef std::pair<format, unsigned> result;
private:
    environment        m_env;
    type_checker       m_tc;
    unsigned           m_num_steps;
    unsigned           m_depth;
    name               m_meta_prefix;
    unsigned           m_next_meta_idx;
    name_map<name>     m_purify_meta_table;
    name_map<name>     m_purify_local_table;
    name_set           m_purify_used_locals;
    // cached configuration
    options            m_options;
    unsigned           m_indent;
    unsigned           m_max_depth;
    unsigned           m_max_steps;
    bool               m_implict;          //!< if true show implicit arguments
    bool               m_unicode;          //!< if true use unicode chars
    bool               m_coercion;         //!< if true show coercions
    bool               m_notation;
    bool               m_universes;
    bool               m_full_names;
    bool               m_private_names;

    unsigned max_bp() const { return std::numeric_limits<unsigned>::max(); }
    name mk_metavar_name(name const & m);
    name mk_local_name(name const & n, name const & suggested);
    level purify(level const & l);
    expr purify(expr const & e);
    result mk_result(format const & e, unsigned rbp) const { return mk_pair(e, rbp); }
    result mk_result(format const & e) const { return mk_result(e, max_bp()); }
    bool is_implicit(expr const & f);
    bool is_prop(expr const & e);

    format pp_binder_block(buffer<name> const & names, expr const & type, binder_info const & bi);
    format pp_binders(buffer<expr> const & locals);
    format pp_level(level const & l);

    result pp_child(expr const & e, unsigned bp);
    result pp_var(expr const & e);
    result pp_sort(expr const & e);
    result pp_const(expr const & e);
    result pp_meta(expr const & e);
    result pp_local(expr const & e);
    result pp_app(expr const & e);
    result pp_lambda(expr const & e);
    result pp_pi(expr const & e);
    result pp_let(expr e);
    result pp_have(expr const & e);
    result pp_show(expr const & e);
    result pp_macro(expr const & e);
    result pp_explicit(expr const & e);
    void set_options_core(options const & o);

public:
    pretty_fn(environment const & env, options const & o);
    result pp(expr const & e);
    void set_options(options const & o);
    options const & get_options() const { return m_options; }
    format operator()(expr const & e);
};

formatter_factory mk_pretty_formatter_factory();
}
