/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/extra_info.h"

namespace lean {
name const & get_extra_info() {
    static name g_extra_info("extra_info");
    static register_annotation_fn g_extra_info_annotation(g_extra_info);
    return g_extra_info;
}
static name g_extra_info_name = get_extra_info(); // force 'extra_info' annotation to be registered

expr mk_extra_info(expr const & e) { return mk_annotation(get_extra_info(), e); }
bool is_extra_info(expr const & e) { return is_annotation(e, get_extra_info()); }
}
