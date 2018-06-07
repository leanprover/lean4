/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "runtime/sstream.h"
#include "library/scope_pos_info_provider.h"

namespace lean {
LEAN_THREAD_PTR(pos_info_provider, g_p);

scope_pos_info_provider::scope_pos_info_provider(pos_info_provider & p):m_old_p(g_p) { g_p = &p; }
scope_pos_info_provider::~scope_pos_info_provider() { g_p = m_old_p; }

pos_info_provider * get_pos_info_provider() {
    return g_p;
}
optional<pos_info> get_pos_info(expr const & e) {
    return get_pos_info_provider() ? get_pos_info_provider()->get_pos_info(e) : optional<pos_info>();
}
optional<pos_info> get_pos_info(optional<expr> const & e) {
    return e ? get_pos_info(*e) : optional<pos_info>();
}

std::string pos_string_for(expr const & e) {
    pos_info_provider * provider = get_pos_info_provider();
    if (!provider) return "'unknown'";
    pos_info pos  = provider->get_pos_info_or_some(e);
    sstream s;
    s << provider->get_file_name() << ":" << pos.first << ":" << pos.second << ":";
    return s.str();
}
}
