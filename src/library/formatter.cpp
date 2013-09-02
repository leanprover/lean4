/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include "formatter.h"
#include "printer.h"
#include "kernel_exception.h"

namespace lean {
class simple_formatter_cell : public formatter_cell {
public:
    virtual format operator()(expr const & e, options const & opts) {
        std::ostringstream s; s << e; return format(s.str());
    }
    virtual format operator()(context const & c, options const & opts) {
        std::ostringstream s; s << c; return format(s.str());
    }
    virtual format operator()(context const & c, expr const & e, bool format_ctx, options const & opts) {
        std::ostringstream s;
        if (format_ctx)
            s << c << "|-\n";
        s << mk_pair(e,c);
        return format(s.str());
    }
    virtual format operator()(object const & obj, options const & opts) {
        std::ostringstream s; s << obj; return format(s.str());
    }
    virtual format operator()(environment const & env, options const & opts) {
        std::ostringstream s; s << env; return format(s.str());
    }
};
formatter mk_simple_formatter() {
    return formatter(new simple_formatter_cell());
}

format formatter::operator()(kernel_exception const & ex, options const & opts) {
    if (unknown_name_exception const * _ex = dynamic_cast<unknown_name_exception const *>(&ex)) {
        return format{format("unknown object '"), format(_ex->get_name()), format("'")};
    } else if (already_declared_exception const * _ex = dynamic_cast<already_declared_exception const *>(&ex)) {
        return format{format("invalid object declaration, environment already has an object named '"),
                format(_ex->get_name()), format("'")};
    } else if (app_type_mismatch_exception const * _ex = dynamic_cast<app_type_mismatch_exception const *>(&ex)) {
        unsigned indent = get_pp_indent(opts);
        format app_f = operator()(_ex->get_context(), _ex->get_application(), false, opts);
        format given_f = operator()(_ex->get_context(), _ex->get_given_type(), false, opts);
        format expected_f = operator()(_ex->get_context(), _ex->get_expected_type(), false, opts);
        unsigned arg_pos = _ex->get_arg_pos();
        return format({format("type mismatch at application argument"), space(), format(arg_pos), space(), format("of"),
                    nest(indent, compose(line(), app_f)),
                    line(), format("expected type"),
                    nest(indent, compose(line(), expected_f)),
                    line(), format("given type"),
                    nest(indent, compose(line(), given_f))});
    } else if (function_expected_exception const * _ex = dynamic_cast<function_expected_exception const *>(&ex)) {
        unsigned indent = get_pp_indent(opts);
        format expr_f = operator()(_ex->get_context(), _ex->get_expr(), false, opts);
        return format({format("function expected at"),
                    nest(indent, compose(line(), expr_f))});
    } else if (type_expected_exception const * _ex = dynamic_cast<type_expected_exception const *>(&ex)) {
        unsigned indent = get_pp_indent(opts);
        format expr_f = operator()(_ex->get_context(), _ex->get_expr(), false, opts);
        return format({format("type expected, got"),
                    nest(indent, compose(line(), expr_f))});
    } else if (def_type_mismatch_exception const * _ex = dynamic_cast<def_type_mismatch_exception const *>(&ex)) {
        unsigned indent = get_pp_indent(opts);
        format name_f  = format(_ex->get_name());
        format type_f  = operator()(_ex->get_type(), opts);
        format value_f = operator()(_ex->get_value_type(), opts);
        return format({format("type mismatch at definition '"), name_f, format("', expected type"),
                    nest(indent, compose(line(), type_f)),
                    line(), format("given type"),
                    nest(indent, compose(line(), value_f))});
    } else {
        return format(ex.what());
    }
}
}
