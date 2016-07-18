/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
namespace lean {
environment add_key_equivalence(environment const & env, name const & n1, name const & n2);
bool is_key_equivalent(environment const & env, name const & n1, name const & n2);
void for_each_key_equivalence(environment const & env, std::function<void(buffer<name> const &)> const & fn);

/** \brief Abstract occurrences of \c t in \c s. We detect subterms equivalent to \c t using key-matching.
    That is, only perform is_def_eq tests when the head symbol of substerm is equivalent to head symbol of \c t.
    New equivalent head symbols can be declared using \c add_key_alias.
    If occs is not none, then only the specified occurrences are abstracted. */
expr kabstract(type_context & ctx, expr const & e, expr const & t, optional<list<unsigned>> const & occs);
inline expr kabstract(type_context & ctx, expr const & e, expr const & t) { return kabstract(ctx, e, t, optional<list<unsigned>>()); }
inline expr kabstract(type_context & ctx, expr const & e, expr const & t, list<unsigned> const & occs) {
    return kabstract(ctx, e, t, optional<list<unsigned>>(occs));
}

void initialize_kabstract();
void finalize_kabstract();
}
