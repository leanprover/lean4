/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
#include "library/tactic/occurrences.h"

namespace lean {
environment add_key_equivalence(environment const & env, name const & n1, name const & n2);
bool is_key_equivalent(environment const & env, name const & n1, name const & n2);
void for_each_key_equivalence(environment const & env, std::function<void(buffer<name> const &)> const & fn);

/** \brief Abstract occurrences of \c t in \c s. We detect subterms equivalent to \c t using key-matching.
    That is, only perform is_def_eq tests when the head symbol of substerm is equivalent to head symbol of \c t.
    New equivalent head symbols can be declared using \c add_key_alias.
    If \c unify is false, then matching is used instead of unification. That is, metavariables occurring in `s` are
    not assigned. */
expr kabstract(type_context_old & ctx, expr const & s, expr const & t, occurrences const & occs, bool unify);
inline expr kabstract(type_context_old & ctx, expr const & s, expr const & t) { return kabstract(ctx, s, t, occurrences(), true); }

void initialize_kabstract();
void finalize_kabstract();
}
