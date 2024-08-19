/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Return true iff \c n is the name of an auxiliary recursor.
    \see add_aux_recursor */
bool is_aux_recursor(environment const & env, name const & n);
bool is_no_confusion(environment const & env, name const & n);
}
