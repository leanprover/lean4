/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "frontends/lean/parser_pos_provider.h"

namespace lean {
struct parameter {
    pos_info    m_pos;
    expr        m_local;
    binder_info m_bi;
    parameter(pos_info const & p, expr const & l, binder_info const & bi):
        m_pos(p), m_local(l), m_bi(bi) {}
    parameter():m_pos(0, 0) {}
};
}
