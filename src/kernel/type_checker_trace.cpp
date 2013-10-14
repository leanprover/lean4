/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker_trace.h"

namespace lean {

void add_pos_info(format & r, expr const & e, pos_info_provider const * p) {
    if (!p)
        return;
    format f = p->pp(e);
    if (!f)
        return;
    r += f;
    r += space();
}

function_expected_trace_cell::~function_expected_trace_cell() {
}

format function_expected_trace_cell::pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool) const {
    unsigned indent = get_pp_indent(opts);
    format expr_fmt = fmt(m_ctx, m_app, false, opts);
    format r;
    add_pos_info(r, get_main_expr(), p);
    r += format("Function expected at");
    r += nest(indent, compose(line(), expr_fmt));
    return r;
}

void function_expected_trace_cell::get_children(buffer<trace_cell*> &) const {
}

expr const & function_expected_trace_cell::get_main_expr() const {
    return m_app;
}

app_type_match_trace_cell::~app_type_match_trace_cell() {
}

format app_type_match_trace_cell::pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool) const {
    unsigned indent = get_pp_indent(opts);
    format r;
    add_pos_info(r, get_main_expr(), p);
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

void app_type_match_trace_cell::get_children(buffer<trace_cell*> &) const {
}

expr const & app_type_match_trace_cell::get_main_expr() const {
    return m_app;
}

type_expected_trace_cell::~type_expected_trace_cell() {
}

format type_expected_trace_cell::pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool) const {
    unsigned indent = get_pp_indent(opts);
    format expr_fmt = fmt(m_ctx, m_type, false, opts);
    format r;
    add_pos_info(r, get_main_expr(), p);
    r += format("Type expected at");
    r += nest(indent, compose(line(), expr_fmt));
    return r;
}

void type_expected_trace_cell::get_children(buffer<trace_cell*> &) const {
}

expr const & type_expected_trace_cell::get_main_expr() const {
    return m_type;
}

def_type_match_trace_cell::~def_type_match_trace_cell() {
}

format def_type_match_trace_cell::pp(formatter const &, options const &, pos_info_provider const * p, bool) const {
    format r;
    add_pos_info(r, get_main_expr(), p);
    r += format("Type of definition '");
    r += format(get_name());
    r += format("' must be convertible to expected type.");
    return r;
}

void def_type_match_trace_cell::get_children(buffer<trace_cell*> &) const {
}

expr const & def_type_match_trace_cell::get_main_expr() const {
    return m_value;
}
}
