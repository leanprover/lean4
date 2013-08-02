/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"
#include "environment.h"
#include "context.h"

namespace lean {
class environment;
/** \brief Normalize e using the environment env and context ctx */
expr normalize(expr const & e, environment const & env, context const & ctx = context());
/** \brief Normalize e using the environment env, context ctx, and add v to "normalization stack" */
expr normalize(expr const & e, environment const & env, context const & ctx, expr const & v);
}
