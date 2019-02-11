/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/annotation.h"

namespace lean {
static name * g_borrowed = nullptr;

expr mk_borrowed(expr const & e) { return mk_annotation(*g_borrowed, e); }
bool is_borrowed(expr const & e) { return is_annotation(e, *g_borrowed); }
expr const & get_borrowed_arg(expr const & e) { lean_assert(is_borrowed(e)); return get_annotation_arg(e); }

void initialize_borrowed_annotation() {
    g_borrowed = new name("borrowed");
    register_annotation(*g_borrowed);
}

void finalize_borrowed_annotation() {
    delete g_borrowed;
}
}
