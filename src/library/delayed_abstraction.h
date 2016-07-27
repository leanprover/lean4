/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
expr mk_delayed_abstraction(expr const & e, buffer<name> const & ns);
expr mk_delayed_abstraction(expr const & e, name const & n);
bool is_delayed_abstraction(expr const & e);
expr const & get_delayed_abstraction_expr(expr const & e);
void get_delayed_abstraction_info(expr const & e, buffer<name> & ns, buffer<expr> & es);
expr push_delayed_abstraction(expr const & e);
expr push_delayed_abstraction(expr const & e, buffer<name> const & ns, buffer<expr> const & es);

/* Create e{ls[0] := ls[0], ..., ls[n-1] := ls[n-1]}
   \pre is_metavar(e)
   \pre for all x in ls, is_local(x) */
expr mk_delayed_abstraction_with_locals(expr const & e, buffer<expr> const & ls);

/* Ceeate e{ns[0] := vs[0], ... ls[n-1] := vs[n-1]}
   \pre is_metavar(e)
   \pre ns.size() == es.size()
   \pre !ns.empty() */
expr mk_delayed_abstraction(expr const & e, buffer<name> const & ns, buffer<expr> const & vs);

void initialize_delayed_abstraction();
void finalize_delayed_abstraction();
}
