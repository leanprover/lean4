/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/flet.h"
#include "library/type_context.h"

namespace lean {
expr type_context::relaxed_whnf(expr const & e) {
    flet<transparency_mode> set(m_transparency_mode, transparency_mode::ALL);
    return whnf(e);
}

bool type_context::relaxed_is_def_eq(expr const & e1, expr const & e2) {
    flet<transparency_mode> set(m_transparency_mode, transparency_mode::ALL);
    return is_def_eq(e1, e2);
}

name type_context::get_local_pp_name(expr const & e) const {
    lean_assert(is_local(e));
    if (is_local_decl_ref(e))
        return m_lctx.get_local_decl(e)->get_name();
    else
        return local_pp_name(e);
}

expr type_context::push_local(name const & pp_name, expr const & type, binder_info const & bi) {
    return m_lctx.mk_local_decl(pp_name, type, bi);
}

void type_context::pop_local() {
    return m_lctx.pop_local_decl();
}
}
