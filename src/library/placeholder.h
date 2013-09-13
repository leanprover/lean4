/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/**
    \brief Return a new placeholder expression. To be able to track location,
    a new constant for each placeholder.
*/
expr mk_placholder();

/**
    \brief Return true iff the given expression is a placeholder.
*/
bool is_placeholder(expr const & e);

/**
    \brief Return true iff the given expression contains placeholders.
*/
bool has_placeholder(expr const & e);
}
