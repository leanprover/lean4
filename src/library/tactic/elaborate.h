/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "library/metavar_context.h"

namespace lean {
expr mk_by(expr const & e);
bool is_by(expr const & e);
expr const & get_by_arg(expr const & e);

/* Elaboration function.
   \remark The boolean flag indicates whether metavariables should be tolerated in the result or not.
   \remark The metavariable context is input/output. */
typedef std::function<expr(environment &, options const &, metavar_context &, local_context const &, expr const &, bool)> elaborate_fn;

/** \brief Auxiliary function for setting the thread local elaboration
    procedure used by the tactic framework. */
class scope_elaborate_fn {
    elaborate_fn const * m_old;
public:
    scope_elaborate_fn(elaborate_fn const &);
    ~scope_elaborate_fn();
};

void initialize_elaborate();
void finalize_elaborate();
}
