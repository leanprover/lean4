/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include "util/sexpr/options.h"
#include "kernel/expr.h"

namespace lean {
/**
    \brief Return the body of the binding \c b, where variable #0 is replaced by a local constant with a "fresh" name.
    The name is considered fresh if it is not used by a constant or local constant occuring in the body of \c b.
    The fresh constant is also returned (second return value).

    \remark If preserve_type is false, then the local constant will not use binding_domain.
*/
std::pair<expr, expr> binding_body_fresh(expr const & b, bool preserve_type = false);

/** \brief Return the body of the let-expression \c l, where variable #0 is replaced by a local constant with a "fresh" name. */
std::pair<expr, expr> let_body_fresh(expr const & l, bool preserve_type = false);

/**
   \brief API for formatting expressions
*/
class formatter_cell {
public:
    virtual ~formatter_cell() {}
    /** \brief Format the given expression. */
    virtual format operator()(environment const & env, expr const & e, options const & opts) const = 0;
};
/**
   \brief Smart-pointer for the actual formatter object (aka \c formatter_cell).
*/
class formatter {
    std::shared_ptr<formatter_cell> m_cell;
    formatter(formatter_cell * c):m_cell(c) {}
public:
    format operator()(environment const & env, expr const & e, options const & opts = options()) const { return (*m_cell)(env, e, opts); }
    template<typename FCell> friend formatter mk_formatter(FCell && fcell);
};

template<typename FCell> formatter mk_formatter(FCell && fcell) {
    return formatter(new FCell(std::forward<FCell>(fcell)));
}

std::ostream & operator<<(std::ostream & out, expr const & e);
/**
   \brief Create a simple formatter object based on operator<<
*/
formatter mk_simple_formatter();

typedef std::function<format(formatter const &, options const &)> pp_fn;
}
