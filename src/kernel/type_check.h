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
expr infer_type(expr const & e, environment const & env, context const & ctx = context());
bool is_convertible(expr const & t1, expr const & t2, environment const & env, context const & ctx = context());
}
