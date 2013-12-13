/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/arith/nat.h"
#include "library/arith/int.h"
#include "library/arith/real.h"
#include "library/arith/special_fn.h"

namespace lean {
class environment;
/**
   \brief Import all arithmetic related builtin libraries.
*/
void import_arith(environment const & env);
}
