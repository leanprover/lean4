/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/name.h"
#include "util/buffer.h"
#include "kernel/expr.h"

namespace lean {
typedef std::pair<unsigned, unsigned> pos_info;
/** \brief Parameter data */
struct parameter {
    pos_info m_pos;
    name     m_name;
    expr     m_type;
    bool     m_implicit;
    parameter(pos_info const & p, name const & n, expr const & t, bool i):m_pos(p), m_name(n), m_type(t), m_implicit(i) {}
    parameter():m_pos(0, 0), m_implicit(false) {}
};
typedef buffer<parameter> parameter_buffer;
}
