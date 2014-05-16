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
// Remark: in a nonempty context C, variable 0 is head(C)
typedef list<binder> context;
inline context extend(context const & c, name const & n, expr const & t) { return cons(binder(n, t), c); }
inline context extend(context const & c, binder const & b) { return cons(b, c); }
binder const & lookup(context const & c, unsigned i);
optional<binder> find(context const & c, unsigned i);
}
