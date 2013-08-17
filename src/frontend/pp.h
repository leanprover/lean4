/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "context.h"

namespace lean {

class frontend;
class expr_formatter {
public:
    virtual ~expr_formatter() {}
    /** \brief Convert expression in the given context into a format object. */
    virtual format operator()(expr const & e, context const & c = context()) = 0;
    /** \brief format a definition. */
    virtual format operator()(char const * kwd, name const & n, expr const & t, expr const & v);
    /** \brief format a postulate. */
    virtual format operator()(char const * kwd, name const & n, expr const & t);

    /** \brief Return options for pretty printing. */
    virtual options get_options() const = 0;

    void pp(std::ostream & out, expr const & e, context const & c);
    void pp(std::ostream & out, expr const & e);

    /** \brief Nest the given format object using the setting provided by get_options. */
    format nest(format const & f);
};
std::shared_ptr<expr_formatter> mk_pp_formatter(frontend const & fe, options const & opts);
}
