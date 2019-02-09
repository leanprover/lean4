/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lean_path.h"
#include "kernel/environment.h"
#include "library/compiler/util.h"

namespace lean {
void emit_cpp(std::ostream & out, environment const & env, module_name const & m, list<module_name> const & deps);
}
