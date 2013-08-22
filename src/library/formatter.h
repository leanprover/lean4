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
class environment;
class object;
/**
   \brief API for formatting expressions, contexts and environments.
*/
class formatter_cell {
public:
    virtual ~formatter_cell() {}
    /** \brief Format the given expression. */
    virtual format operator()(expr const & e, options const & opts) = 0;
    /** \brief Format the given context. */
    virtual format operator()(context const & c, options const & opts) = 0;
    /**
        \brief Format the given expression with respect to the given
        context.

        \remark If format_ctx == false, then the context is not formatted. It just provides names
        for the free variables
    */
    virtual format operator()(context const & c, expr const & e, bool format_ctx, options const & opts) = 0;
    /** \brief Format the given object */
    virtual format operator()(object const & obj, options const & opts) = 0;
    /** \brief Format the given environment */
    virtual format operator()(environment const & env, options const & opts) = 0;
};

class formatter {
    std::shared_ptr<formatter_cell> m_cell;
public:
    formatter(formatter_cell * c):m_cell(c) {}
    formatter(std::shared_ptr<formatter_cell> const & c):m_cell(c) {}
    format operator()(expr const & e, options const & opts = options()) { return (*m_cell)(e, opts); }
    format operator()(context const & c, options const & opts = options()) { return (*m_cell)(c, opts); }
    format operator()(context const & c, expr const & e, bool format_ctx = false, options const & opts = options()) { return (*m_cell)(c, e, format_ctx, opts); }
    format operator()(object const & obj, options const & opts = options()) { return (*m_cell)(obj, opts); }
    format operator()(environment const & env, options const & opts = options()) { return (*m_cell)(env, opts); }
};

formatter mk_simple_formatter();
}
