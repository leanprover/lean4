/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "lean_elaborator_exception.h"
#include "lean_elaborator.h"

namespace lean {
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

format pp(formatter fmt, elaborator_exception const & ex, options const & opts) {
    unsigned indent = get_pp_indent(opts);
    context const & ctx = ex.get_context();
    if (overload_exception const * _ex = dynamic_cast<overload_exception const *>(&ex)) {
        format r;
        r += format{format(ex.what()), line(), format("Candidates:")};
        r += pp(fmt, ctx, _ex->get_fs(), _ex->get_f_types(), opts);
        r += format{line(), format("Arguments:")};
        r += pp(fmt, ctx, _ex->get_args(), _ex->get_arg_types(), opts);
        return r;
    } else {
        format expr_f = fmt(ctx, ex.get_expr(), false, opts);
        format elb_f  = ex.get_elaborator().pp(fmt, opts);
        return format({format(ex.what()), space(), format("at term"),
                    nest(indent, compose(line(), expr_f)),
                    line(), format("Elaborator state"),
                    nest(indent, compose(line(), elb_f))});
    }
}

regular const & operator<<(regular const & out, elaborator_exception const & ex) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_regular_channel().get_stream() << mk_pair(pp(out.m_state.get_formatter(), ex, opts), opts);
    return out;
}

diagnostic const & operator<<(diagnostic const & out, elaborator_exception const & ex) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_diagnostic_channel().get_stream() << mk_pair(pp(out.m_state.get_formatter(), ex, opts), opts);
    return out;
}
}
