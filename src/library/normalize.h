/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "kernel/abstract_type_context.h"

namespace lean {
/** \brief Return the \c e normal form with respect to the environment \c env. */
expr normalize(environment const & env, expr const & e, bool eta = false);
expr normalize(abstract_type_context & ctx, expr const & e, bool eta = false);
}
