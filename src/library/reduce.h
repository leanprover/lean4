/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_set.h"
#include "kernel/context.h"
#include "kernel/environment.h"

namespace lean {
bool is_head_beta(expr const & t);
expr head_beta_reduce(expr const & t);
expr head_reduce(expr const & t, environment const & e, context const & c = context(), name_set const * defs = nullptr);
}
