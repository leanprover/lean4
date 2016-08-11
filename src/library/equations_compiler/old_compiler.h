/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/equations_compiler/equations.h"
namespace lean {
expr compile_equations(old_type_checker & tc, io_state const & ios, expr const & eqns,
                       expr const & meta, expr const & meta_type);
}
