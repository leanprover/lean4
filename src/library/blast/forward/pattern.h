/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Annotate \c e as a pattern hint */
expr mk_pattern_hint(expr const & e);
/** \brief Return true iff \c e is an annotated pattern */
bool is_pattern_hint(expr const & e);
/** \brief Return the actual pattern */
expr const & get_pattern_hint_arg(expr const & e);
/** \brief Return true iff \c e contains pattern hints */
bool has_pattern_hints(expr const & e);

/** \brief Hint for the pattern inference procedure.
    It should not consider/infer patterns containing the constant \c n. */
environment add_no_pattern(environment const & env, name const & n, bool persistent);
/** \brief Return true if constant \c n is marked as [no_pattern] in the given environment. */
bool is_no_pattern(environment const & env, name const & n);
/** \brief Return the set of constants marked as no-patterns */
name_set const & get_no_patterns(environment const & env);

void initialize_pattern();
void finalize_pattern();
}
