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
// Maps based on structural equality. That is, two keys are equal iff they are structurally equal
template<typename T>
using expr_map = typename std::unordered_map<expr, T, expr_hash, std::equal_to<expr>>;
// The following map also takes into account binder information
template<typename T>
using expr_bi_map = typename std::unordered_map<expr, T, expr_hash, is_bi_equal_proc>;

template<typename T>
class expr_cond_bi_map : public std::unordered_map<expr, T, expr_hash, is_cond_bi_equal_proc> {
public:
    expr_cond_bi_map(bool use_bi = false):
        std::unordered_map<expr, T, expr_hash, is_cond_bi_equal_proc>(10, expr_hash(), is_cond_bi_equal_proc(use_bi)) {}
};
};
