/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_map>
#include <functional>
#include "kernel/expr.h"

namespace lean {
// Maps based on pointer equality. That is, two keys are equal iff they are pointer equal
template<typename T>
using expr_map = typename std::unordered_map<expr, T, expr_hash_alloc, expr_eqp>;

template<typename T>
using expr_cell_map = typename std::unordered_map<expr_cell *, T, expr_cell_hash, expr_cell_eqp>;

// Maps based on structural equality. That is, two keys are equal iff they are structurally equal
template<typename T>
using expr_struct_map = typename std::unordered_map<expr, T, expr_hash, std::equal_to<expr>>;
// The following map also takes into account binder information
template<typename T>
using expr_bi_struct_map = typename std::unordered_map<expr, T, expr_hash, is_bi_equal_proc>;
};
