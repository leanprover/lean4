/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
class type_context_old;
class abstract_context_cache;
/** \brief Mark sub-expressions of \c e that are computationally irrelevant. */
expr mark_comp_irrelevant_subterms(environment const & env, abstract_context_cache & cache, expr const & e);
/** \brief Mark the given term as computationally irrelevant */
expr mark_comp_irrelevant(expr const & e);
/** \brief Return true iff \c e is annotated with the comp-irrelevant annotation */
bool is_marked_as_comp_irrelevant(expr const & e);
/** \brief Return true iff the type of \c e is a sort or a proposition */
bool is_comp_irrelevant(type_context_old & ctx, expr const & e);
void initialize_comp_irrelevant();
void finalize_comp_irrelevant();
}
