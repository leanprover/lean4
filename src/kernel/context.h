/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/list.h"
#include "util/optional.h"
#include "kernel/expr.h"

namespace lean {
typedef list<std::pair<name, expr>> context;
inline context extend(context const & c, name const & n, expr const & t) { return cons(mk_pair(n, t), c); }
std::pair<name, expr> const & lookup(context const & c, unsigned i);
optional<std::pair<name, expr>> find(context const & c, unsigned i);
}
