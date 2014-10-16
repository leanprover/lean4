/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/extra_info.h"

namespace lean {
static name * g_extra_info = nullptr;
name const & get_extra_info() { return *g_extra_info; }

expr mk_extra_info(expr const & e, tag g) { return mk_annotation(get_extra_info(), e, g); }
expr mk_extra_info(expr const & e) { return mk_annotation(get_extra_info(), e); }
bool is_extra_info(expr const & e) { return is_annotation(e, get_extra_info()); }

void initialize_extra_info() {
    g_extra_info = new name("extra_info");
    register_annotation(*g_extra_info);
}

void finalize_extra_info() {
    delete g_extra_info;
}
}
