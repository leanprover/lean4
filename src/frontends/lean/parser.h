/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>

namespace lean {
class script_state;
class frontend;
class io_state;
class environment;
/** \brief Functional object for parsing commands and expressions */
class parser {
    class imp;
    std::unique_ptr<imp> m_ptr;
public:
    parser(frontend & fe, std::istream & in, script_state * S, bool use_exceptions = true, bool interactive = false);
    ~parser();

    /** \brief Parse a sequence of commands */
    bool operator()();

    /** \brief Parse a single expression */
    expr parse_expr();
};

/** \brief Implements the Read Eval Print loop */
class shell {
    frontend &            m_frontend;
    script_state *        m_script_state;
public:
    shell(frontend & fe, script_state * S);
    ~shell();

    bool operator()();
};

bool parse_commands(frontend & fe, std::istream & in, script_state * S = nullptr, bool use_exceptions = true, bool interactive = false);
bool parse_commands(environment const & env, io_state & st, std::istream & in, script_state * S = nullptr, bool use_exceptions = true, bool interactive = false);
expr parse_expr(frontend & fe, std::istream & in, script_state * S = nullptr, bool use_exceptions = true);
expr parse_expr(environment const & env, io_state & st, std::istream & in, script_state * S = nullptr, bool use_exceptions = true);
}
