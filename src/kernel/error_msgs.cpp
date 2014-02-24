/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/error_msgs.h"

namespace lean {
static format pp_indent_expr(formatter const & fmt, options const & opts, expr const & e) {
    return nest(get_pp_indent(opts), compose(line(), fmt(e, opts)));
}

format pp_type_expected(formatter const & fmt, options const & opts, expr const & e) {
    return compose(format("type expected at"), pp_indent_expr(fmt, opts, e));
}

format pp_function_expected(formatter const & fmt, options const & opts, expr const & e) {
    return compose(format("function expected at"), pp_indent_expr(fmt, opts, e));
}

format pp_pair_expected(formatter const & fmt, options const & opts, expr const & e) {
    return compose(format("pair expected at"), pp_indent_expr(fmt, opts, e));
}

format pp_app_type_mismatch(formatter const & fmt, options const & opts, expr const & app,
                            expr const & expected_type, expr const & given_type) {
    format r;
    r += format("type mismatch at application");
    r += pp_indent_expr(fmt, opts, app);
    r += format("expected type:");
    r += pp_indent_expr(fmt, opts, expected_type);
    r += format("given type:");
    r += pp_indent_expr(fmt, opts, given_type);
    return r;
}

format pp_proj_type_mismatch(formatter const & fmt, options const & opts, expr const & proj,
                             expr const & arg_type) {
    format r;
    r += format("type mismatch at projection");
    r += pp_indent_expr(fmt, opts, proj);
    r += format("pair expected, given type:");
    r += pp_indent_expr(fmt, opts, arg_type);
    return r;
}

format pp_def_type_mismatch(formatter const & fmt, options const & opts, name const & n,
                            expr const & expected_type, expr const & given_type) {
    format r("type mismatch at definition '");
    r += format(n);
    r += format("', expected type");
    r += pp_indent_expr(fmt, opts, expected_type);
    r += compose(line(), format("given type:"));
    r += pp_indent_expr(fmt, opts, given_type);
    return r;
}
}
