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
/* Given a delayed abstraction `[delayed t, h_1 := e_1, ..., h_n := e_n]`, push
   the delayed substitutions `h_i := e_i` to the metavariables occurring in `t`.

   Remark: if `t` is a metavariable, then we just return `e`. */
expr push_delayed_abstraction(expr const & e);
/* Append the new delayed substitutions `ns[i] := es[i]` to the metavariables occurring in `e`.

   \pre ns.size() == es.size() */
expr append_delayed_abstraction(expr const & e, buffer<name> const & ns, buffer<expr> const & es);

/* Create e{ls[0] := ls[0], ..., ls[n-1] := ls[n-1]}
   \pre is_metavar(e)
   \pre for all x in ls, is_local(x) */
expr mk_delayed_abstraction_with_locals(expr const & e, buffer<expr> const & ls);

/* Ceeate e{ns[0] := vs[0], ... ls[n-1] := vs[n-1]}
   \pre is_metavar(e)
   \pre ns.size() == es.size()
   \pre !ns.empty() */
expr mk_delayed_abstraction(expr const & e, buffer<name> const & ns, buffer<expr> const & vs);

class metavar_context;

/* Similar to abstract_locals, but create a delayed_abstraction macro around metavariables
   occurring in \c e. */
expr delayed_abstract_locals(metavar_context const & mctx, expr const & e, unsigned nlocals, expr const * locals);

void initialize_delayed_abstraction();
void finalize_delayed_abstraction();
}
