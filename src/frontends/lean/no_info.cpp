/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/no_info.h"

namespace lean {
name const & get_no_info() {
    static name g_no_info("no_info");
    static register_annotation_fn g_no_info_annotation(g_no_info);
    return g_no_info;
}
static name g_no_info_name = get_no_info(); // force 'no_info' annotation to be registered

expr mk_no_info(expr const & e) { return mk_annotation(get_no_info(), e); }
bool is_no_info(expr const & e) { return is_annotation(e, get_no_info()); }
}
