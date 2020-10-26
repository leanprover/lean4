/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Return true iff the given environment contains a sorry macro. */
bool has_sorry(environment const & env);
bool has_sorry(expr const &);
bool has_sorry(declaration const &);
bool has_synthetic_sorry(expr const &);

/** \brief Return true iff \c e is a sorry macro. */
bool is_sorry(expr const & e);
/** \brief Return true iff \c e is a synthetic sorry macro */
bool is_synthetic_sorry(expr const & e);
/** \brief Type of the sorry macro. */
expr const & sorry_type(expr const & sry);
void initialize_sorry();
void finalize_sorry();
}
