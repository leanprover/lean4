/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr_formatter.h"

namespace lean {
std::shared_ptr<expr_formatter> mk_pp_expr_formatter(frontend const & fe, options const & opts);
}
