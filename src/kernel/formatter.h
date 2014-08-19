/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include "util/sexpr/options.h"

namespace lean {
class expr;
class environment;

/** \brief Return true iff \c t contains a constant named \c n or a local constant with named (pp or not) \c n */
bool is_used_name(expr const & t, name const & n);
/**
    \brief Return the body of the binding \c b, where variable #0 is replaced by a local constant with a "fresh" name.
    The name is considered fresh if it is not used by a constant or local constant occuring in the body of \c b.
    The fresh constant is also returned (second return value).

    \remark If preserve_type is false, then the local constant will not use binding_domain.
*/
pair<expr, expr> binding_body_fresh(expr const & b, bool preserve_type = false);

/** \brief Return the body of the let-expression \c l, where variable #0 is replaced by a local constant with a "fresh" name. */
pair<expr, expr> let_body_fresh(expr const & l, bool preserve_type = false);

class formatter {
    std::function<format(expr const &, options const &)> m_fn;
    options                             m_options;
public:
    formatter(options const & o, std::function<format(expr const &, options const &)> const & fn):m_fn(fn), m_options(o) {}
    format operator()(expr const & e) const { return m_fn(e, m_options); }
    options const & get_options() const { return m_options; }
    formatter update_options(options const & o) const { return formatter(o, m_fn); }
};

typedef std::function<formatter(environment const &, options const &)> formatter_factory;

std::ostream & operator<<(std::ostream & out, expr const & e);
/** \brief Create a simple formatter object based on operator */
formatter_factory mk_simple_formatter_factory();

typedef std::function<format(formatter const &)> pp_fn;
}
