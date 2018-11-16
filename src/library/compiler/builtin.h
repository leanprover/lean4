/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
namespace lean {
optional<expr> get_builtin_constant_ll_type(name const & c);
optional<unsigned> get_builtin_constant_arity(name const & c);
void initialize_builtin();
void finalize_builtin();
}
