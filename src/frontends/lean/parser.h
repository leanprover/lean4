/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include "util/lua.h"
#include "kernel/environment.h"
#include "library/io_state.h"

namespace lean {
class script_state;
/** \brief Functional object for parsing commands and expressions */
class parser {
public:
    class imp;
private:
    std::unique_ptr<imp> m_ptr;
public:
    parser(environment const & env, io_state const & st, std::istream & in, script_state * S, bool use_exceptions = true, bool interactive = false);
    parser(environment const & env, std::istream & in, script_state * S, bool use_exceptions = true, bool interactive = false);
    ~parser();

    /** \brief Parse a sequence of commands */
    bool operator()();

    /** \brief Parse a single expression */
    expr parse_expr();

    io_state get_io_state() const;
};

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

bool parse_commands(environment const & env, io_state & st, std::istream & in, script_state * S = nullptr, bool use_exceptions = true, bool interactive = false);
expr parse_expr(environment const & env, io_state & st, std::istream & in, script_state * S = nullptr, bool use_exceptions = true);

void open_macros(lua_State * L);
}
