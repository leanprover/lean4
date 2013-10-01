/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker_trace.h"

namespace lean {

function_expected_trace_cell::~function_expected_trace_cell() {
}

format function_expected_trace_cell::pp(formatter const & fmt, options const & opts) const {
    unsigned indent = get_pp_indent(opts);
    format expr_fmt = fmt(m_ctx, m_app, false, opts);
    format r;
    r += format("function expected at");
    r += nest(indent, compose(line(), expr_fmt));
    return r;
}

void function_expected_trace_cell::get_children(buffer<trace> &) const {
}

expr const & function_expected_trace_cell::get_main_expr() const {
    return m_app;
}

app_type_match_trace_cell::~app_type_match_trace_cell() {
}

format app_type_match_trace_cell::pp(formatter const & fmt, options const & opts) const {
    unsigned indent = get_pp_indent(opts);
    format app_fmt  = fmt(m_ctx, m_app, false, opts);
    format r;
    r += format("type of argument ");
    r += format(m_i);
    r += format(" of application");
    r += nest(indent, compose(line(), app_fmt));
    return r;
}

void app_type_match_trace_cell::get_children(buffer<trace> &) const {
}

expr const & app_type_match_trace_cell::get_main_expr() const {
    return m_app;
}

type_expected_trace_cell::~type_expected_trace_cell() {
}

format type_expected_trace_cell::pp(formatter const & fmt, options const & opts) const {
    unsigned indent = get_pp_indent(opts);
    format expr_fmt = fmt(m_ctx, m_type, false, opts);
    format r;
    r += format("type expected at");
    r += nest(indent, compose(line(), expr_fmt));
    return r;
}

void type_expected_trace_cell::get_children(buffer<trace> &) const {
}

expr const & type_expected_trace_cell::get_main_expr() const {
    return m_type;
}

def_type_match_trace_cell::~def_type_match_trace_cell() {
}

format def_type_match_trace_cell::pp(formatter const &, options const &) const {
    format r;
    r += format("type of definition of '");
    r += format(get_name());
    r += format("'");
    return r;
}

void def_type_match_trace_cell::get_children(buffer<trace> &) const {
}

expr const & def_type_match_trace_cell::get_main_expr() const {
    return m_value;
}
}
