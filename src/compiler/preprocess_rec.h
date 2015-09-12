/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Expand user-defined and auxiliary recursors, simplify declaration,
    put definition in eta-expanded normal form, and
    eliminate nested (recursive) recursor applications.
    Each nested recursive application becomes a new definition.

    All new declarations are added to the resulting environment.
    \remark The new declaration corresponding to \c d is in the last one in \c new_decls.
*/
environment preprocess_rec(environment const & env, declaration const & d, buffer<name> & new_decls);

void initialize_preprocess_rec();
void finalize_preprocess_rec();
}
