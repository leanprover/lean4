/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
namespace lean {
class parser;
void check_atomic(name const & n);
void check_in_section(parser const & p);
bool is_root_namespace(name const & n);
name remove_root_prefix(name const & n);
}
