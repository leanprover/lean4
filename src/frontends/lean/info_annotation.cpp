/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/info_annotation.h"

namespace lean {
static name * g_no_info = nullptr;
name const & get_no_info() { return *g_no_info; }

expr mk_no_info(expr const & e) { return mk_annotation(get_no_info(), e); }
bool is_no_info(expr const & e) { return is_annotation(e, get_no_info()); }

static name * g_extra_info = nullptr;
name const & get_extra_info() { return *g_extra_info; }

expr mk_extra_info(expr const & e, tag g) { return mk_annotation(get_extra_info(), e, g); }
expr mk_extra_info(expr const & e) { return mk_annotation(get_extra_info(), e); }
bool is_extra_info(expr const & e) { return is_annotation(e, get_extra_info()); }

static name * g_notation_info = nullptr;
name const & get_notation_info() { return *g_notation_info; }

expr mk_notation_info(expr const & e, tag g) { return mk_annotation(get_notation_info(), e, g); }
expr mk_notation_info(expr const & e) { return mk_annotation(get_notation_info(), e); }
bool is_notation_info(expr const & e) { return is_annotation(e, get_notation_info()); }

void initialize_info_annotation() {
    g_no_info = new name("no_info");
    register_annotation(*g_no_info);
    g_extra_info = new name("extra_info");
    register_annotation(*g_extra_info);
    g_notation_info = new name("notation_info");
    register_annotation(*g_notation_info);
}

void finalize_info_annotation() {
    delete g_no_info;
    delete g_extra_info;
    delete g_notation_info;
}
}
