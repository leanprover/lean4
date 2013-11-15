/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include "frontends/lean/frontend.h"

namespace lean {
class script_evaluator;
/** \brief Functional object for parsing commands and expressions */
class parser {
    class imp;
    std::unique_ptr<imp> m_ptr;
public:
    parser(frontend & fe, std::istream & in, script_evaluator * S, bool use_exceptions = true, bool interactive = false);
    ~parser();

    /** \brief Parse a sequence of commands */
    bool operator()();

    /** \brief Parse a single expression */
    expr parse_expr();
};

/** \brief Implements the Read Eval Print loop */
class shell {
    frontend &                m_frontend;
    script_evaluator *        m_script_evaluator;
public:
    shell(frontend & fe, script_evaluator * S);
    ~shell();

    bool operator()();
};

inline bool parse_commands(frontend & fe, std::istream & in, script_evaluator * S = nullptr, bool use_exceptions = true, bool interactive = false) {
    return parser(fe, in, S, use_exceptions, interactive)();
}
inline expr parse_expr(frontend & fe, std::istream & in) {
    return parser(fe, in, nullptr).parse_expr();
}
}
