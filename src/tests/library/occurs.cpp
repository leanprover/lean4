/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/abstract.h"
#include "library/occurs.h"
#include "kernel/init_module.h"
#include "library/init_module.h"
using namespace lean;

static void tst1() {
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr Type = mk_Type();
    expr T = Type;
    expr a1 = Local("a", T);
    lean_assert(occurs(f, f));
    lean_assert(!occurs(a, f));
    lean_assert(occurs(a, mk_app(f, a)));
    lean_assert(occurs("a", mk_app(f, a)));
    lean_assert(!occurs("b", f));
    lean_assert(!occurs(a, Fun(a1, mk_app(f, a1))));
}

int main() {
    save_stack_info();
    initialize_util_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    initialize_library_module();
    tst1();
    finalize_library_module();
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
