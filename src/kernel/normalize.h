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
/** \brief Normalize \c e using the environment \c env and context \c ctx */
expr normalize(expr const & e, environment const & env, context const & ctx = context());
}
