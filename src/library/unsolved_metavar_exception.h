/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/exception.h"
#include "util/sstream.h"
#include "kernel/expr.h"

namespace lean {
/**
   \brief Auxiliary exception used to sign that an expression still contains unsolved metavariables after
   elaboration, solving, etc.
*/
class unsolved_metavar_exception : public exception {
    expr m_expr;
public:
    unsolved_metavar_exception(char const * msg, expr const & e):exception(msg), m_expr(e) {}
    unsolved_metavar_exception(sstream const & strm, expr const & e):exception(strm), m_expr(e) {}
    virtual ~unsolved_metavar_exception() {}
    expr get_expr() const { return m_expr; }
    virtual throwable * clone() const { return new unsolved_metavar_exception(m_msg.c_str(), m_expr); }
    virtual void rethrow() const { throw *this; }
};
}
