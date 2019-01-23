/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <fstream>
#include "library/compiler/emit_cpp.h"

namespace lean {
environment emit_cpp(environment const & env, comp_decls const &) {
    // TODO(Leo)
    return env;
}

void print_cpp_code(std::ofstream & out, environment const & /* env */) {
    out << "// Lean compiler output\n";
    // TODO(Leo)
}
}
