/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include "kernel/expr.h"
#include "util/options.h"

namespace lean {
std::ostream & operator<<(std::ostream & out, expr const & e);
void set_print_fn(std::function<void(std::ostream &, expr const &)> const & fn);

void initialize_formatter();
void finalize_formatter();
}
