/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"

namespace lean {
/**
    \brief Return true iff the given expression is of the form:

    ((fun (x : A), B) Arg)
*/
bool is_head_beta(expr const & e);
/** \brief Apply head beta-reduction to the given expression. */
expr head_beta(expr const & e);
};
