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
environment emit_cpp(environment const & env, comp_decls const & ds);
void print_cpp_code(std::ofstream & out, environment const & env, module_name const & m, list<module_name> const & deps);
}
