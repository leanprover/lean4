/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/object.h"

namespace lean {
extern "C" object* lean_expr_local(object*, object*, object*, uint8) {
    lean_unreachable();
    return nullptr;
}

extern "C" object* lean_environment_mk_empty(object*) {
    lean_unreachable();
    return nullptr;
}

extern "C" uint8 lean_environment_contains(object*, object*) {
    lean_unreachable();
    return 0;
}

extern "C" object* lean_elaborator_elaborate_command(object*, object*, object*) {
    lean_unreachable();
    return nullptr;
}
}
