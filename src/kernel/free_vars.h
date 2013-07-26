/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"
namespace lean {
/**
   \brief Return true if the given expression has free variables.
*/
bool has_free_vars(expr const & a);
/**
   \brief Return true if the given expression does not have free variables.
*/
inline bool closed(expr const & a) { return !has_free_vars(a); }
}
