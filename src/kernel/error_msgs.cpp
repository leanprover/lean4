/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/error_msgs.h"

namespace lean {
format pp_indent_expr(formatter const & fmt, expr const & e) {
    return nest(get_pp_indent(fmt.get_options()), compose(line(), fmt(e)));
}

format pp_type_expected(formatter const & fmt, expr const & e) {
    return compose(format("type expected at"), pp_indent_expr(fmt, e));
}

format pp_function_expected(formatter const & fmt, expr const & e) {
    return compose(format("function expected at"), pp_indent_expr(fmt, e));
}

format pp_app_type_mismatch(formatter const & fmt, expr const & app, expr const & expected_type, expr const & given_type) {
    format r;
    r += format("type mismatch at application");
    r += pp_indent_expr(fmt, app);
    r += compose(line(), format("expected type:"));
    r += pp_indent_expr(fmt, expected_type);
    r += compose(line(), format("given type:"));
    r += pp_indent_expr(fmt, given_type);
    return r;
}

format pp_def_type_mismatch(formatter const & fmt, name const & n, expr const & expected_type, expr const & given_type) {
    format r("type mismatch at definition '");
    r += format(n);
    r += format("', expected type");
    r += pp_indent_expr(fmt, expected_type);
    r += compose(line(), format("given type:"));
    r += pp_indent_expr(fmt, given_type);
    return r;
}

format pp_type_mismatch(formatter const & fmt, expr const & expected_type, expr const & given_type) {
    format r("type mismatch, expected type");
    r += ::lean::pp_indent_expr(fmt, expected_type);
    r += compose(line(), format("given type:"));
    r += ::lean::pp_indent_expr(fmt, given_type);
    return r;
}

format pp_decl_has_metavars(formatter const & fmt, name const & n, expr const & e, bool is_type) {
    format r("failed to add declaration '");
    r += format(n);
    r += format("' to environment, ");
    if (is_type)
        r += format("type");
    else
        r += format("value");
    r += format(" has metavariables");
    r += pp_indent_expr(fmt, e);
    return r;
}
}
