/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/** \brief Return a shallow copy of \c e */
expr copy(expr const & e);

/**
    \brief Return a new expression that is equal to the given
    argument, but does not share any memory cell with it.
*/
expr deep_copy(expr const & e);
}
