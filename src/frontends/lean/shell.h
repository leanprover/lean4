/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/parser.h"

namespace lean {
/** \brief Implements the Read Eval Print loop */
class shell {
    environment    m_env;
    io_state       m_io_state;
    script_state * m_script_state;
public:
    shell(environment const & env, io_state const & st, script_state * S);
    shell(environment const & env, script_state * S);
    ~shell();

    bool operator()();
    io_state get_io_state() const { return m_io_state; }
};
}
