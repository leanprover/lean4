/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/pos_info_provider.h"
namespace lean {
struct procedure {
    name               m_name;
    optional<pos_info> m_pos;
    expr               m_code;
    procedure(name const & n, optional<pos_info> const & pos, expr const & code):
        m_name(n), m_pos(pos), m_code(code) {}
};
}
