/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "lean_elaborator_exception.h"
#include "lean_elaborator.h"

namespace lean {
format pp_elaborator_state(formatter fmt, elaborator const & elb, options const & opts) {
    unsigned indent     = get_pp_indent(opts);
    format r;
    if (elb.has_constraints()) {
        format elb_fmt  = elb.pp(fmt, opts);
        r += compose(line(), format("Elaborator state"));
        r += nest(indent, compose(line(), elb_fmt));
    }
    return r;
}

format pp(formatter fmt, context const & ctx, std::vector<expr> const & exprs, std::vector<expr> const & types, options const & opts) {
    unsigned indent = get_pp_indent(opts);
    lean_assert(exprs.size() == types.size());
    auto it1 = exprs.begin();
    auto it2 = types.begin();
    format r;
    for (; it1 != exprs.end(); ++it1, ++it2) {
        r += nest(indent, compose(line(), group(format{fmt(ctx, *it1, false, opts), space(), colon(),
                                                       nest(indent, format{line(), fmt(ctx, *it2, false, opts)})})));
    }
    return r;
}

format elaborator_exception::pp(formatter const & fmt, options const & opts) const {
    unsigned indent  = get_pp_indent(opts);
    format expr_fmt  = fmt(get_context(), get_expr(), false, opts);
    format r;
    r += format{format(what()), space(), format("at term")};
    r += nest(indent, compose(line(), expr_fmt));
    r += pp_elaborator_state(fmt, get_elaborator(), opts);
    return r;
}

format overload_exception::pp(formatter const & fmt, options const & opts) const {
    context const & ctx = get_context();
    format r;
    r += format{format(what()), line(), format("Candidates:")};
    r += ::lean::pp(fmt, ctx, get_fs(), get_f_types(), opts);
    r += format{line(), format("Arguments:")};
    r += ::lean::pp(fmt, ctx, get_args(), get_arg_types(), opts);
    return r;
}

format unification_app_mismatch_exception::pp(formatter const & fmt, options const & opts) const {
    unsigned indent     = get_pp_indent(opts);
    auto const & ctx    = get_context();
    expr const & app    = get_expr();
    auto args_it        = get_args().begin();
    auto args_end       = get_args().end();
    auto types_it       = get_types().begin();
    format app_fmt      = fmt(ctx, app, false, opts);
    format r            = format{format(what()), nest(indent, compose(line(), app_fmt))};
    format fun_type_fmt = fmt(ctx, *types_it, false, opts);
    r += compose(line(), format("Function type:"));
    r += nest(indent, compose(line(), fun_type_fmt));
    ++args_it;
    ++types_it;
    if (get_args().size() > 2)
        r += compose(line(), format("Arguments types:"));
    else
        r += compose(line(), format("Argument type:"));
    for (; args_it != args_end; ++args_it, ++types_it) {
        format arg_fmt    = fmt(ctx, *args_it, false, opts);
        format type_fmt   = fmt(ctx, *types_it, false, opts);
        r += nest(indent, compose(line(), group(format{arg_fmt, space(), colon(), nest(indent, format{line(), type_fmt})})));
    }
    r += pp_elaborator_state(fmt, get_elaborator(), opts);
    return r;
}

format unification_type_mismatch_exception::pp(formatter const & fmt, options const & opts) const {
    unsigned indent     = get_pp_indent(opts);
    auto const & ctx    = get_context();
    expr const & e      = get_expr();
    expr const & p      = get_processed_expr();
    expr const & exp    = get_expected_type();
    expr const & given  = get_given_type();
    format r            = format{format(what()), nest(indent, compose(line(), fmt(ctx, e, false, opts)))};
    if (p != e) {
        r += compose(line(), format("Term after elaboration:"));
        r += nest(indent, compose(line(), fmt(ctx, p, false, opts)));
    }
    r += compose(line(), format("Expected type:"));
    r += nest(indent, compose(line(), fmt(ctx, exp, false, opts)));
    if (given) {
        r += compose(line(), format("Got:"));
        r += nest(indent, compose(line(), fmt(ctx, given, false, opts)));
    }
    r += pp_elaborator_state(fmt, get_elaborator(), opts);
    return r;
}

regular const & operator<<(regular const & out, elaborator_exception const & ex) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_regular_channel().get_stream() << mk_pair(ex.pp(out.m_state.get_formatter(), opts), opts);
    return out;
}

diagnostic const & operator<<(diagnostic const & out, elaborator_exception const & ex) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_diagnostic_channel().get_stream() << mk_pair(ex.pp(out.m_state.get_formatter(), opts), opts);
    return out;
}
}
