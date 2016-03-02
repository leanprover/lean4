/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/annotation.h"

namespace lean {
static name * g_begin_end = nullptr;
static name * g_begin_end_element = nullptr;

expr mk_begin_end_annotation(expr const & e) { return mk_annotation(*g_begin_end, e, nulltag); }
expr mk_begin_end_element_annotation(expr const & e) { return mk_annotation(*g_begin_end_element, e, nulltag); }
bool is_begin_end_annotation(expr const & e) { return is_annotation(e, *g_begin_end); }
bool is_begin_end_element_annotation(expr const & e) { return is_annotation(e, *g_begin_end_element); }

void initialize_begin_end_annotation() {
    g_begin_end  = new name("begin_end");
    g_begin_end_element = new name("begin_end_element");
    register_annotation(*g_begin_end);
    register_annotation(*g_begin_end_element);
}

void finalize_begin_end_annotation() {
    delete g_begin_end;
    delete g_begin_end_element;
}
}
