/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "lean_elaborator_exception.h"
#include "lean_elaborator.h"

namespace lean {
format pp(formatter fmt, elaborator_exception const & ex, options const & opts) {
    unsigned indent = get_pp_indent(opts);
    format expr_f = fmt(ex.get_context(), ex.get_expr(), false, opts);
    format elb_f  = ex.get_elaborator().pp(fmt, opts);
    return format({format(ex.what()), space(), format("at term"),
                nest(indent, compose(line(), expr_f)),
                line(), format("Elaborator state"),
                nest(indent, compose(line(), elb_f))});
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
