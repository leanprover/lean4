/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/compiler/procedure.h"
namespace lean {
/** \brief Expand user-defined and auxiliary recursors, simplify declaration,
    put definition in eta-expanded normal form, and
    eliminate nested (recursive) recursor applications.
    Nested recurse applications become new procedures. */
void preprocess(environment const & env, declaration const & d, buffer<procedure> & result);

/** \brief Similar to previous function, but supports a collection \c ds of potentially mutually recursive
    definitions. */
void preprocess(environment const & env, buffer<declaration> const & ds, buffer<procedure> & result);

void initialize_preprocess();
void finalize_preprocess();
}
