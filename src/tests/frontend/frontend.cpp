/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontend.h"
#include "environment.h"
#include "test.h"
using namespace lean;

static void tst1() {
    frontend f;
    f.add_uvar("tst");
    frontend c = f.mk_child();
    lean_assert(c.get_uvar("tst") == f.get_uvar("tst"));
    lean_assert(f.env().has_children());
}

int main() {
    continue_on_violation(true);
    tst1();
    return has_violations() ? 1 : 0;
}
