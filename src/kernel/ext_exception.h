/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/exception.h"
#include "util/sexpr/options.h"
#include "kernel/formatter.h"
#include "kernel/expr.h"

namespace lean {
/** \brief Base class for exceptions with support for pretty printing. */
class ext_exception : public exception {
public:
    ext_exception() {}
    ext_exception(char const * msg):exception(msg) {}
    ext_exception(sstream const & strm):exception(strm) {}
    virtual ~ext_exception() noexcept {}
    /** \brief Return a reference (if available) to the main expression associated with this exception.
        This information is used to provide better error messages. */
    virtual optional<expr> get_main_expr() const { return none_expr(); }
    virtual format pp(formatter const &) const { return format(what()); }
    virtual throwable * clone() const { return new ext_exception(m_msg.c_str()); }
    virtual void rethrow() const { throw *this; }
};
}
