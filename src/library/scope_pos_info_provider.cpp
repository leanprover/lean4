/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/scope_pos_info_provider.h"

namespace lean {
LEAN_THREAD_PTR(pos_info_provider, g_p);

scope_pos_info_provider::scope_pos_info_provider(pos_info_provider & p):m_old_p(g_p) { g_p = &p; }
scope_pos_info_provider::~scope_pos_info_provider() { g_p = m_old_p; }

pos_info_provider * get_pos_info_provider() {
    return g_p;
}
}
