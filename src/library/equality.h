/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/expr_pair.h"

namespace lean {
bool is_equality(expr const & e);
bool is_equality(expr const & e, expr & lhs, expr & rhs);
expr_pair get_equality_args(expr const & e);
}
