/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/expr_pair.h"

namespace lean {
bool is_eq_heq(expr const & e);
expr_pair eq_heq_args(expr const & e);
}
