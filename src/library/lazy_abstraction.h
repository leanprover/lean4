/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
expr mk_lazy_abstraction(list<pair<name, unsigned>> const & s, expr const & e);
expr mk_lazy_abstraction(name const & n, expr const & e);
bool is_lazy_abstraction(expr const & e);
list<pair<name, unsigned>> const & get_lazy_abstraction_info(expr const & e);
expr const & get_lazy_abstraction_expr(expr const & e);
expr push_lazy_abstraction(expr const & e);
void initialize_lazy_abstraction();
void finalize_lazy_abstraction();
}
