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
environment preprocess(environment const & env, constant_info const & info, buffer<procedure> & result);

/** \brief Similar to previous function, but supports a collection \c ds of potentially mutually recursive
    definitions. */
environment preprocess(environment const & env, buffer<constant_info> const & infos, buffer<procedure> & result);

void initialize_preprocess();
void finalize_preprocess();
}
