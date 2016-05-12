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
*/
void preprocess(environment const & env, declaration const & d, buffer<pair<name, expr>> & result);

void initialize_preprocess();
void finalize_preprocess();
}
