/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/sstream.h"
#include "kernel/ext_exception.h"
#include "kernel/pos_info_provider.h"

namespace lean {
class generic_exception : public ext_exception {
protected:
    optional<expr> m_main_expr;
    pp_fn          m_pp_fn;
public:
    generic_exception(char const * msg, optional<expr> const & m, pp_fn const & fn):
        ext_exception(msg), m_main_expr(m), m_pp_fn(fn) {}
    generic_exception(optional<expr> const & m, pp_fn const & fn):
        ext_exception(), m_main_expr(m), m_pp_fn(fn) {}
    virtual ~generic_exception() noexcept {}
    virtual optional<expr> get_main_expr() const override { return m_main_expr; }
    virtual format pp(formatter const & fmt) const override { return m_pp_fn(fmt); }
    virtual throwable * clone() const override { return new generic_exception(m_msg.c_str(), m_main_expr, m_pp_fn); }
    virtual void rethrow() const override { throw *this; }
};

[[ noreturn ]] void throw_generic_exception(char const * msg, optional<expr> const & m);
[[ noreturn ]] void throw_generic_exception(sstream const & strm, optional<expr> const & m);
[[ noreturn ]] void throw_generic_exception(char const * msg, expr const & m);
[[ noreturn ]] void throw_generic_exception(sstream const & strm, expr const & m);
[[ noreturn ]] void throw_generic_exception(char const * msg, optional<expr> const & m, pp_fn const & fn);
[[ noreturn ]] void throw_generic_exception(char const * msg, expr const & m, pp_fn const & fn);
[[ noreturn ]] void throw_generic_exception(optional<expr> const & m, pp_fn const & fn);
[[ noreturn ]] void throw_generic_exception(expr const & m, pp_fn const & fn);

/** \brief Lean exception occurred when parsing file. */
class parser_nested_exception : public exception {
    std::shared_ptr<throwable>          m_exception;
    std::shared_ptr<pos_info_provider>  m_provider;
public:
    parser_nested_exception(std::shared_ptr<throwable> const & ex, std::shared_ptr<pos_info_provider> const & pr):
        exception("parser exception"), m_exception(ex), m_provider(pr) {}
    virtual ~parser_nested_exception() {}
    virtual throwable * clone() const { return new parser_nested_exception(m_exception, m_provider); }
    virtual void rethrow() const { throw *this; }
    virtual char const * what() const noexcept { return m_exception->what(); }
    throwable const & get_exception() const { return *(m_exception.get()); }
    pos_info_provider const & get_provider() const { return *(m_provider.get()); }
};
}
