/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"

namespace lean {
/**
   \brief The resultant expression is structurally identical to the input one, but
   it uses maximally shared sub-expressions.
*/
expr max_sharing(expr const & a);
}
