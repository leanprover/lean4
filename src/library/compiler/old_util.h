/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/compiler/util.h"
namespace lean {
class type_context_old;
/** \brief Create a new name of the form prefix.suffix_idx that is not the name of a declaration and/or VM function.
    It also updates the index idx. */
name mk_compiler_unused_name(environment const & env, name const & prefix, char const * suffix, unsigned & idx);

/** \brief Return true iff \c e is computationally irrelevant */
bool is_comp_irrelevant(type_context_old & ctx, expr const & e);

unsigned get_constructor_arity(environment const & env, name const & n);

/** \brief Return true iff \c n is an auxiliary cases_on recursor */
bool is_cases_on_recursor(environment const & env, name const & n);
}
