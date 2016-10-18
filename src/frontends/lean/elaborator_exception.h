/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/sstream.h"
#include "library/io_state.h"

namespace lean {
class elaborator_exception : public formatted_exception {
public:
    elaborator_exception(optional<expr> const & e, format const & fmt):formatted_exception(e, fmt) {}
    elaborator_exception(expr const & e, format const & fmt):formatted_exception(e, fmt) {}
    elaborator_exception(expr const & e, sstream const & strm):formatted_exception(e, format(strm.str())) {}
    elaborator_exception(expr const & e, char const * msg):formatted_exception(e, format(msg)) {}
    virtual throwable * clone() const override;
    virtual void rethrow() const override { throw *this; }
};

class nested_elaborator_exception : public elaborator_exception {
    std::shared_ptr<elaborator_exception> m_exception;
    nested_elaborator_exception(optional<expr> const & ref, format const & fmt,
                                std::shared_ptr<elaborator_exception> const & ex):
        elaborator_exception(ref, fmt), m_exception(ex) {}
public:
    nested_elaborator_exception(optional<expr> const & ref, elaborator_exception const & ex, format const & fmt):
        elaborator_exception(ref, fmt),
        m_exception(static_cast<elaborator_exception*>(ex.clone())) {}
    nested_elaborator_exception(expr const & ref, elaborator_exception const & ex, format const & fmt):
        nested_elaborator_exception(some_expr(ref), ex, fmt) {}
    virtual void rethrow() const override { throw *this; }
    virtual throwable * clone() const override;
    virtual optional<expr> get_main_expr() const override;
    virtual format pp() const override;
};
}
