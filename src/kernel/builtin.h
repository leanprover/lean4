/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"

namespace lean {
expr bool_type();
bool is_bool_type(expr const & e);

expr bool_value(bool v);
bool is_bool_value(expr const & e);
bool to_bool(expr const & e);
bool is_true(expr const & e);
bool is_false(expr const & e);
}
