/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "context.h"

namespace lean {
class environment;
/**
   \brief API for formatting expressions, contexts and environments.
*/
class formatter {
public:
    virtual ~formatter() {}
    /** \brief Format the given expression. */
    virtual format operator()(expr const & e) = 0;
    /** \brief Format the given context. */
    virtual format operator()(context const & c) = 0;
    /**
        \brief Format the given expression with respect to the given
        context.

        \remark If format_ctx == false, then the context is not formatted. It just provides names
        for the free variables
    */
    virtual format operator()(context const & c, expr const & e, bool format_ctx = false) = 0;
    /** \brief Format the given environment */
    virtual format operator()(environment const & env) = 0;
};
/**
   \brief Return simple expression formatter that just uses printer module.
*/
std::shared_ptr<formatter> mk_simple_formatter();
}
