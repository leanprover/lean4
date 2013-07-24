/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_map>
#include "expr.h"

namespace lean {

template<typename T>
using expr_map = typename std::unordered_map<expr, T, expr_hash, expr_eqp>;

template<typename T>
using expr_offset_map = typename std::unordered_map<expr_offset, T, expr_offset_hash, expr_offset_eqp>;

template<typename T>
using expr_cell_map = typename std::unordered_map<expr_cell *, T, expr_cell_hash, expr_cell_eqp>;

template<typename T>
using expr_cell_offset_map = typename std::unordered_map<expr_cell_offset, T, expr_cell_offset_hash, expr_cell_offset_eqp>;

};
