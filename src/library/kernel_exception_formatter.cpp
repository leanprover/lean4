/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel_exception_formatter.h"

namespace lean {
/*
  The following ad-hoc dynamic dispatch is ugly, but we can't define
  pp as a virtual method in kernel_exception because
  the formatter is not part of the kernel.
*/
format pp(formatter const & fmt, kernel_exception const & ex, options const & opts) {
    if (unknown_name_exception const * _ex = dynamic_cast<unknown_name_exception const *>(&ex))
        return pp(*_ex, opts);
    else if (already_declared_exception const * _ex = dynamic_cast<already_declared_exception const *>(&ex))
        return pp(*_ex, opts);
    else if (app_type_mismatch_exception const * _ex = dynamic_cast<app_type_mismatch_exception const *>(&ex))
        return pp(fmt, *_ex, opts);
    else if (function_expected_exception const * _ex = dynamic_cast<function_expected_exception const *>(&ex))
        return pp(fmt, *_ex, opts);
    else if (type_expected_exception const * _ex = dynamic_cast<type_expected_exception const *>(&ex))
        return pp(fmt, *_ex, opts);
    else if (def_type_mismatch_exception const * _ex = dynamic_cast<def_type_mismatch_exception const *>(&ex))
        return pp(fmt, *_ex, opts);
    else
        return format(ex.what());
}

format pp(unknown_name_exception const & ex, options const & opts) {
    return format{format("unknown object '"), format(ex.get_name()), format("'")};
}

format pp(already_declared_exception const & ex, options const & opts) {
    return format{format("invalid object declaration, environment already has an object named '"), format(ex.get_name()), format("'")};
}

format pp(formatter const & fmt, app_type_mismatch_exception const & ex, options const & opts) {
    unsigned indent     = get_pp_indent(opts);
    context const & ctx = ex.get_context();
    expr const & app    = ex.get_application();
    format app_fmt      = fmt(ctx, app, false, opts);
    std::vector<expr> const & arg_types = ex.get_arg_types();
    auto it = arg_types.begin();
    format f_type_fmt   = fmt(ctx, *it, false, opts);
    format arg_types_fmt;
    ++it;
    for (unsigned i = 1; it != arg_types.end(); ++it, ++i) {
        expr const & a    = arg(app, i);
        format arg_fmt    = fmt(ctx, a, false, opts);
        if (is_pi(a) || is_lambda(a) || is_let(a))
            arg_fmt = paren(arg_fmt);
        format arg_type_fmt = fmt(ctx, *it, false, opts);
        arg_types_fmt += nest(indent, compose(line(), group(format{arg_fmt, space(), colon(), nest(indent, format{line(), arg_type_fmt})})));
    }
    format r;
    r += format("type mismatch at application");
    r += nest(indent, compose(line(), app_fmt));
    r += compose(line(), format("Function type:"));
    r += nest(indent, compose(line(), f_type_fmt));
    r += line();
    if (arg_types.size() > 2)
        r += format("Arguments types:");
    else
        r += format("Argument type:");
    r += arg_types_fmt;
    return r;
}

format pp(formatter const & fmt, function_expected_exception const & ex, options const & opts) {
    unsigned indent = get_pp_indent(opts);
    format expr_fmt = fmt(ex.get_context(), ex.get_expr(), false, opts);
    format r;
    r += format("function expected at");
    r += nest(indent, compose(line(), expr_fmt));
    return r;
}

format pp(formatter const & fmt, type_expected_exception const & ex, options const & opts) {
    unsigned indent = get_pp_indent(opts);
    format expr_fmt = fmt(ex.get_context(), ex.get_expr(), false, opts);
    format r;
    r += format("type expected, got");
    r += nest(indent, compose(line(), expr_fmt));
    return r;
}

format pp(formatter const & fmt, def_type_mismatch_exception const & ex, options const & opts) {
    unsigned indent  = get_pp_indent(opts);
    format r;
    r += format("type mismatch at definition '");
    r += format(ex.get_name());
    r += format("', expected type");
    r += nest(indent, compose(line(), fmt(ex.get_type(), opts)));
    r += compose(line(), format("Given type:"));
    r += nest(indent, compose(line(), fmt(ex.get_value_type(), opts)));
    return r;
}

regular const & operator<<(regular const & out, kernel_exception const & ex) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_regular_channel().get_stream() << mk_pair(pp(out.m_state.get_formatter(), ex, opts), opts);
    return out;
}

diagnostic const & operator<<(diagnostic const & out, kernel_exception const & ex) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_diagnostic_channel().get_stream() << mk_pair(pp(out.m_state.get_formatter(), ex, opts), opts);
    return out;
}
}
