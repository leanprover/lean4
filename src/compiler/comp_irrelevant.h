/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Mark sub-expressions of \c e that are computationally irrelevant. */
expr mark_comp_irrelevant(environment const & env, expr const & e);
/** \brief Return true iff \c e is annotated with the comp-irrelevant annotation */
bool is_comp_irrelevant(expr const & e);
void initialize_comp_irrelevant();
void finalize_comp_irrelevant();
}
