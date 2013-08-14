/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "context.h"
#include "options.h"

namespace lean {
/** \brief Abstract class for formatting expressions. */
class expr_formatter {
public:
    virtual ~expr_formatter() {}
    /** \brief Convert expression in the given context into a format object. */
    virtual format operator()(expr const & e, context const & c) = 0;
    /** \brief Return options for pretty printing. */
    virtual options get_options() const = 0;

    void pp(std::ostream & out, expr const & e, context const & c);
    void pp(std::ostream & out, expr const & e);

    /** \brief Nest the given format object using the setting provided by get_options. */
    format nest(format const & f);
};

/**
    \brief Create simple expression formatter.
    It is mainly useful for pretty printing.
*/
std::shared_ptr<expr_formatter> mk_simple_expr_formatter();
std::ostream & operator<<(std::ostream & out, std::pair<expr_formatter &, expr const &> const & p);
}
