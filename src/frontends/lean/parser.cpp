/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/io_state_stream.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/parser_imp.h"

namespace lean {
parser::parser(environment const & env, io_state const & ios, std::istream & in, script_state * S, bool use_exceptions, bool interactive) {
    parser_imp::show_prompt(interactive, ios);
    m_ptr.reset(new parser_imp(env, ios, in, S, use_exceptions, interactive));
}

parser::parser(environment const & env, std::istream & in, script_state * S, bool use_exceptions, bool interactive):
    parser(env, io_state(), in, S, use_exceptions, interactive) {
    m_ptr->m_io_state.set_formatter(mk_pp_formatter(m_ptr->m_env));
}

parser::~parser() {
}

bool parser::operator()() {
    return m_ptr->parse_commands();
}

expr parser::parse_expr() {
    return m_ptr->parse_expr_main();
}

io_state parser::get_io_state() const {
    return m_ptr->m_io_state;
}

bool parse_commands(environment const & env, io_state & ios, std::istream & in, script_state * S, bool use_exceptions, bool interactive) {
    parser p(env, ios, in, S, use_exceptions, interactive);
    bool r = p();
    ios = p.get_io_state();
    return r;
}

expr parse_expr(environment const & env, io_state & ios, std::istream & in, script_state * S, bool use_exceptions) {
    parser p(env, ios, in, S, use_exceptions);
    expr r = p.parse_expr();
    ios = p.get_io_state();
    return r;
}
}
