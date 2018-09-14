/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "runtime/sstream.h"
#include "library/ext_exception.h"
#include "library/scope_pos_info_provider.h"

namespace lean {
class generic_exception : public ext_exception {
protected:
    optional<pos_info> m_pos;
    pp_fn              m_pp_fn;
public:
    generic_exception(char const * msg, optional<pos_info> const & p, pp_fn const & fn):
        ext_exception(msg), m_pos(p), m_pp_fn(fn) {}
    generic_exception(char const * msg, optional<expr> const & m, pp_fn const & fn):
        generic_exception(msg, get_pos_info(m), fn) {}
    generic_exception(optional<pos_info> const & p, pp_fn const & fn):
            ext_exception(), m_pos(p), m_pp_fn(fn) {}
    generic_exception(optional<expr> const & m, pp_fn const & fn):
        ext_exception(), m_pos(get_pos_info(m)), m_pp_fn(fn) {}
    generic_exception(optional<expr> const & m, char const * msg);
    generic_exception(optional<expr> const & m, sstream const & strm):generic_exception(m, strm.str().c_str()) {}
    explicit generic_exception(char const * msg):generic_exception(none_expr(), msg) {}
    explicit generic_exception(sstream const & strm):generic_exception(none_expr(), strm) {}
    generic_exception(expr const & m, char const * msg):generic_exception(some_expr(m), msg) {}
    generic_exception(expr const & m, sstream const & strm):generic_exception(some_expr(m), strm) {}
    generic_exception(expr const & m, pp_fn const & fn):generic_exception(some_expr(m), fn) {}

    virtual optional<pos_info> get_pos() const override { return m_pos; }
    virtual format pp(formatter const & fmt) const override { return m_pp_fn(fmt); }
};

class nested_exception : public generic_exception {
protected:
    std::exception_ptr m_exception;
public:
    nested_exception(optional<pos_info> const & p, pp_fn const & fn, std::exception_ptr const & ex):
        generic_exception(p, fn), m_exception(ex) {}
    nested_exception(optional<expr> const & m, pp_fn const & fn, std::exception_ptr const & ex):
        generic_exception(m, fn), m_exception(ex) {}
    nested_exception(optional<expr> const & m, char const * msg, std::exception_ptr const & ex):
        generic_exception(m, msg), m_exception(ex) {}
    nested_exception(optional<expr> const & m, sstream const & strm, std::exception_ptr const & ex):
        generic_exception(m, strm), m_exception(ex) {}
    explicit nested_exception(char const * msg, std::exception_ptr const & ex):
        nested_exception(none_expr(), msg, ex) {}
    explicit nested_exception(format const & fmt, std::exception_ptr const & ex):
        nested_exception(none_expr(), [=](formatter const &) { return fmt; }, ex) {}
    explicit nested_exception(sstream const & strm, std::exception_ptr const & ex):
        nested_exception(none_expr(), strm, ex) {}
    virtual ~nested_exception() noexcept {}

    virtual optional<pos_info> get_pos() const override;
    virtual format pp(formatter const & fmt) const override;

    std::exception_ptr const & get_exception() const { return m_exception; }
};
}
