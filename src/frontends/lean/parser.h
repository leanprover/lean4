/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include "util/lua.h"
#include "kernel/environment.h"
#include "kernel/io_state.h"

namespace lean {
class script_state;
class parser_imp;
/** \brief Functional object for parsing commands and expressions */
class parser {
private:
    std::unique_ptr<parser_imp> m_ptr;
public:
    parser(environment const & env, io_state const & st, std::istream & in, char const * strm_name, script_state * S, bool use_exceptions = true, bool interactive = false);
    ~parser();

    /** \brief Parse a sequence of commands */
    bool operator()();

    /** \brief Parse a single expression */
    expr parse_expr();

    io_state get_io_state() const;
};

bool parse_commands(environment const & env, io_state & st, std::istream & in, char const * strm_name, script_state * S = nullptr, bool use_exceptions = true, bool interactive = false);
bool parse_commands(environment const & env, io_state & st, char const * fname, script_state * S = nullptr, bool use_exceptions = true, bool interactive = false);
expr parse_expr(environment const & env, io_state & st, std::istream & in, char const * strm_name, script_state * S = nullptr, bool use_exceptions = true);
void open_macros(lua_State * L);
}
