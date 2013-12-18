/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_map>
#include "kernel/expr.h"
#include "library/expr_pair.h"
namespace lean {
// Map based on structural equality
template<typename T>
using expr_pair_struct_map = std::unordered_map<expr_pair, T, expr_pair_hash, expr_pair_eq>;
}
