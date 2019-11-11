/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/abstract.h"
#include "library/abstract_type_context.h"

namespace lean {
expr abstract_type_context::push_local(name const & pp_name, expr const & type, binder_info bi) {
    return mk_local(next_name(), pp_name, type, bi);
}

void abstract_type_context::pop_local() {
    /* do nothing */
}

push_local_fn::~push_local_fn() {
    for (unsigned i = 0; i < m_counter; i++)
        m_ctx.pop_local();
}
}
