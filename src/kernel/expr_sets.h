/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <functional>
#include "util/alloc.h"
#include "runtime/hash.h"
#include "kernel/expr.h"

namespace lean {
typedef lean::unordered_set<expr, expr_hash, std::equal_to<expr>> expr_set;
}
