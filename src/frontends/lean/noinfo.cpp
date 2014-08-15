/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/noinfo.h"

namespace lean {
name const & get_noinfo() {
    static name g_noinfo("noinfo");
    static register_annotation_fn g_noinfo_annotation(g_noinfo);
    return g_noinfo;
}
static name g_noinfo_name = get_noinfo(); // force 'noinfo' annotation to be registered

expr mk_noinfo(expr const & e) { return mk_annotation(get_noinfo(), e); }
bool is_noinfo(expr const & e) { return is_annotation(e, get_noinfo()); }
}
