/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
namespace lean {
expr elim_dead_let(expr const & e);
void initialize_elim_dead_let();
void finalize_elim_dead_let();
}
