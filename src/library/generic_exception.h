/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/sstream.h"
#include "kernel/expr.h"
#include "kernel/formatter.h"

namespace lean {
class generic_exception : public exception {
protected:
    optional<expr> m_main_expr;
    pp_fn          m_pp_fn;
public:
    generic_exception(char const * msg, optional<expr> const & m, pp_fn const & fn):
        exception(msg), m_main_expr(m), m_pp_fn(fn) {}
    generic_exception(optional<expr> const & m, pp_fn const & fn):
        exception(), m_main_expr(m), m_pp_fn(fn) {}
    virtual ~generic_exception() noexcept {}
    virtual optional<expr> get_main_expr() const { return m_main_expr; }
    virtual format pp(formatter const & fmt) const { return m_pp_fn(fmt); }
    virtual throwable * clone() const { return new generic_exception(m_msg.c_str(), m_main_expr, m_pp_fn); }
    virtual void rethrow() const { throw *this; }
};

[[ noreturn ]] void throw_generic_exception(char const * msg, optional<expr> const & m);
[[ noreturn ]] void throw_generic_exception(sstream const & strm, optional<expr> const & m);
[[ noreturn ]] void throw_generic_exception(char const * msg, expr const & m);
[[ noreturn ]] void throw_generic_exception(sstream const & strm, expr const & m);
[[ noreturn ]] void throw_generic_exception(char const * msg, optional<expr> const & m, pp_fn const & fn);
[[ noreturn ]] void throw_generic_exception(char const * msg, expr const & m, pp_fn const & fn);
[[ noreturn ]] void throw_generic_exception(optional<expr> const & m, pp_fn const & fn);
[[ noreturn ]] void throw_generic_exception(expr const & m, pp_fn const & fn);
}
