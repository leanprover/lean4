/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "metavar_env.h"

namespace lean {
/**
   \brief Expression elaborator, it is responsible for "filling" holes
   in terms left by the user. This is the main module resposible for computing
   the value of implicit arguments.
*/
class elaborator {
    environment & m_env;
    metavar_env   m_metaenv;

    expr lookup(context const & c, unsigned i);
    void unify(expr const & e1, expr const & e2, context const & ctx);
    expr check_pi(expr const & e, context const & ctx);
    level check_universe(expr const & e, context const & ctx);
    expr process(expr const & e, context const & ctx);

public:
    elaborator(environment & env);
    metavar_env & menv() { return m_metaenv; }
    expr operator()(expr const & e);
};
}
