/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/abstract.h"
#include "library/abstract_type_context.h"

namespace lean {
push_local_fn::~push_local_fn() {
    for (unsigned i = 0; i < m_counter; i++)
        m_ctx.pop_local();
}
}
