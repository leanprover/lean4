/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_set>
#include <utility>
#include <functional>
#include "util/hash.h"
#include "kernel/expr.h"

namespace lean {
typedef std::unordered_set<expr, expr_hash, std::equal_to<expr>> expr_set;
}
