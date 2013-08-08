/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"
#include "format.h"

namespace lean {
class environment;
format pp(expr const & n);
format pp(expr const & n, environment const & env);
}
