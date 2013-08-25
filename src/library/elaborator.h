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
    environment const & m_env;
    metavar_env         m_metaenv;

    expr lookup(context const & c, unsigned i);
    void unify(expr const & e1, expr const & e2, context const & ctx);
    expr check_pi(expr const & e, context const & ctx);
    level check_universe(expr const & e, context const & ctx);
    expr process(expr const & e, context const & ctx);

public:
    elaborator(environment const & env);
    expr operator()(expr const & e);

    metavar_env & menv() { return m_metaenv; }

    void clear() { m_metaenv.clear(); }
    expr mk_metavar(context const & ctx) { return m_metaenv.mk_metavar(ctx); }

    void set_interrupt(bool flag) { m_metaenv.set_interrupt(flag); }
    void interrupt() { set_interrupt(true); }
    void reset_interrupt() { set_interrupt(false); }

    void display(std::ostream & out) const { m_metaenv.display(out); }
};

/** \brief Return true iff \c e is a special constant used to mark application of overloads. */
bool is_overload_marker(expr const & e);
/** \brief Return the overload marker */
expr mk_overload_marker();
}
