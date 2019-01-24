/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <fstream>
#include "runtime/utf8.h"
#include "library/module.h"
#include "library/compiler/emit_cpp.h"

namespace lean {
environment emit_cpp(environment const & env, comp_decls const & /* ds */) {
    // TODO(Leo)
    return env;
}

void print_cpp_code(std::ofstream & out, environment const & /* env */, module_name const & m, list<module_name> const & deps) {
    out << "// Lean compiler output\n";
    out << "// Module: " << m << "\n";
    out << "// Imports:"; for (module_name const & d : deps) out << " " << d; out << "\n";
    // TODO(Leo)
}
}
