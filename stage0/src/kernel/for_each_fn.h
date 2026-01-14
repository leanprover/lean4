/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include <functional>
#include "runtime/buffer.h"
#include "kernel/expr.h"
#include "kernel/expr_sets.h"

namespace lean {
/**
\brief Expression visitor.

The argument \c f must be a lambda (function object) containing the method

<code>
bool operator()(expr const & e, unsigned offset)
</code>

The \c offset is the number of binders under which \c e occurs.
*/
void for_each(expr const & e, std::function<bool(expr const &, unsigned)> && f); // NOLINT

void for_each(expr const & e, std::function<bool(expr const &)> && f); // NOLINT
}
