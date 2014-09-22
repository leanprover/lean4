/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/no_info.h"

namespace lean {
static name * g_no_info = nullptr;
name const & get_no_info() { return *g_no_info; }

expr mk_no_info(expr const & e) { return mk_annotation(get_no_info(), e); }
bool is_no_info(expr const & e) { return is_annotation(e, get_no_info()); }

void initialize_no_info() {
    g_no_info = new name("no_info");
    register_annotation(*g_no_info);
}

void finalize_no_info() {
    delete g_no_info;
}
}
