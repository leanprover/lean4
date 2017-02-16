/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/pos_info_provider.h"

namespace lean {
class scope_pos_info_provider {
    pos_info_provider * m_old_p;
public:
    scope_pos_info_provider(pos_info_provider & p);
    ~scope_pos_info_provider();
};

pos_info_provider * get_pos_info_provider();
optional<pos_info> get_pos_info(expr const & e);
optional<pos_info> get_pos_info(optional<expr> const & e);
std::string pos_string_for(expr const & e);
}
