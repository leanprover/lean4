/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "expr.h"

namespace lean {
/**
    \brief Abstract class that specifies the API to retrieve
    expression location (line and position).
*/
class expr_locator {
public:
    virtual ~expr_locator();
    /** \brief Return true iff the expression has location information associated with it. */
    virtual bool has_location(expr const & e) const;
    /** \brief Return location (line, pos) associated with expression. \pre has_location() */
    virtual std::pair<unsigned, unsigned> get_location(expr const & e) const;
};
/**
   \brief Create a expression locator s.t. has_location always return false.
*/
std::shared_ptr<expr_locator> mk_dummy_expr_locator();

/**
   \brief Throw an exception with the given msg, and include location
   of the given expression (if available).
*/
void throw_exception(expr_locator const & loc, expr const & src, char const * msg);
void throw_exception(expr_locator const & loc, expr const & src, format const & msg);
}
