/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/exception.h"
#include "kernel/expr.h"

namespace lean {
class blast_exception : public exception {
    expr m_expr;
public:
    blast_exception(char const * msg, expr const & e):exception(msg), m_expr(e) {}
    blast_exception(std::string const & msg, expr const & e):exception(msg), m_expr(e) {}
    virtual ~blast_exception() {}
    virtual throwable * clone() const { return new blast_exception(m_msg, m_expr); }
    virtual void rethrow() const { throw *this; }
};
}
