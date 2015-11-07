/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Return true iff the given environment has <tt>sorry.{l} : Pi {A : Type.{l}}, A</tt> */
bool has_sorry(environment const & env);

/** \brief Declare <tt>sorry.{l} : Pi {A : Type.{l}}, A</tt> in the given environment if it doesn't already contain it.
    Throw an exception if the environment already contains a declaration named \c sorry. */
environment declare_sorry(environment const & env);

/** \brief Return the constant \c sorry */
expr mk_sorry();
/** \brief Return true iff \c e is a sorry expression */
bool is_sorry(expr const & e);
void initialize_sorry();
void finalize_sorry();
}
