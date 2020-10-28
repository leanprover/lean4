/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/annotation.h"
#include "library/compiler/util.h"
#include "library/compiler/llnf.h"
#include "library/compiler/extern_attribute.h"
#include "library/compiler/export_attribute.h"

namespace lean {
static name * g_borrowed = nullptr;

expr mk_borrowed(expr const & e) { return mk_annotation(*g_borrowed, e); }

/*
The new and old frontend use different approaches more annotating expressions.
We use the following hacks to make sure we recognize both of them at `is_borrowed`.
*/
extern "C" uint8 lean_is_marked_borrowed(lean_object * o);

bool is_borrowed(expr const & e) {
    expr e2 = e;
    return is_annotation(e2, *g_borrowed) || lean_is_marked_borrowed(e2.to_obj_arg());
}
expr get_borrowed_arg(expr const & e) {
    lean_assert(is_borrowed(e));
    expr e2 = e;
    return mdata_expr(e2);
}

void initialize_borrowed_annotation() {
    g_borrowed = new name("borrowed");
    mark_persistent(g_borrowed->raw());
    register_annotation(*g_borrowed);
}

void finalize_borrowed_annotation() {
    delete g_borrowed;
}
}
