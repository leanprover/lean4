/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker_justification.h"

namespace lean {

function_expected_justification_cell::~function_expected_justification_cell() {
}

format function_expected_justification_cell::pp_header(formatter const & fmt, options const & opts) const {
    unsigned indent = get_pp_indent(opts);
    format expr_fmt = fmt(m_ctx, m_app, false, opts);
    format r;
    r += format("Function expected at");
    r += nest(indent, compose(line(), expr_fmt));
    return r;
}

void function_expected_justification_cell::get_children(buffer<justification_cell*> &) const {
}

expr const & function_expected_justification_cell::get_main_expr() const {
    return m_app;
}

app_type_match_justification_cell::~app_type_match_justification_cell() {
}

format app_type_match_justification_cell::pp_header(formatter const & fmt, options const & opts) const {
    unsigned indent = get_pp_indent(opts);
    format r;
    r += format("Type of argument ");
    r += format(m_i);
    r += format(" must be convertible to the expected type in the application of");
    r += nest(indent, compose(line(), fmt(m_ctx, arg(m_app, 0), false, opts)));
    unsigned num = num_args(m_app);
    r += line();
    if (num == 2)
        r += format("with argument:");
    else
        r += format("with arguments:");
    for (unsigned i = 1; i < num; i++)
        r += nest(indent, compose(line(), fmt(m_ctx, arg(m_app, i), false, opts)));
    return r;
}

void app_type_match_justification_cell::get_children(buffer<justification_cell*> &) const {
}

expr const & app_type_match_justification_cell::get_main_expr() const {
    return m_app;
}

type_expected_justification_cell::~type_expected_justification_cell() {
}

format type_expected_justification_cell::pp_header(formatter const & fmt, options const & opts) const {
    unsigned indent = get_pp_indent(opts);
    format expr_fmt = fmt(m_ctx, m_type, false, opts);
    format r;
    r += format("Type expected at");
    r += nest(indent, compose(line(), expr_fmt));
    return r;
}

void type_expected_justification_cell::get_children(buffer<justification_cell*> &) const {
}

expr const & type_expected_justification_cell::get_main_expr() const {
    return m_type;
}

def_type_match_justification_cell::~def_type_match_justification_cell() {
}

format def_type_match_justification_cell::pp_header(formatter const &, options const &) const {
    format r;
    r += format("Type of definition '");
    r += format(get_name());
    r += format("' must be convertible to expected type.");
    return r;
}

void def_type_match_justification_cell::get_children(buffer<justification_cell*> &) const {
}

expr const & def_type_match_justification_cell::get_main_expr() const {
    return m_value;
}
}
