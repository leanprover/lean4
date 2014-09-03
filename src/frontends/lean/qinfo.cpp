/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/qinfo.h"

namespace lean {
name const & get_qinfo() {
    static name g_qinfo("qinfo");
    static register_annotation_fn g_qinfo_annotation(g_qinfo);
    return g_qinfo;
}
static name g_qinfo_name = get_qinfo(); // force 'qinfo' annotation to be registered

expr mk_qinfo(expr const & e) { return mk_annotation(get_qinfo(), e); }
bool is_qinfo(expr const & e) { return is_annotation(e, get_qinfo()); }
}
