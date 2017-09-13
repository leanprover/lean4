/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/sstream.h"
#include "kernel/ext_exception.h"
#include "kernel/scope_pos_info_provider.h"

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
    virtual throwable * clone() const override { return new generic_exception(m_msg.c_str(), m_pos, m_pp_fn); }
    virtual void rethrow() const override { throw *this; }
};

class nested_exception : public generic_exception {
protected:
    std::shared_ptr<throwable>          m_exception;
public:
    nested_exception(optional<pos_info> const & p, pp_fn const & fn, throwable const & ex):
            generic_exception(p, fn), m_exception(std::shared_ptr<throwable>(ex.clone())) {}
    nested_exception(optional<expr> const & m, pp_fn const & fn, throwable const & ex):
        generic_exception(m, fn), m_exception(std::shared_ptr<throwable>(ex.clone())) {}
    nested_exception(optional<expr> const & m, char const * msg, throwable const & ex):
        generic_exception(m, msg), m_exception(std::shared_ptr<throwable>(ex.clone())) {}
    nested_exception(optional<expr> const & m, sstream const & strm, throwable const & ex):
        generic_exception(m, strm), m_exception(std::shared_ptr<throwable>(ex.clone())) {}
    explicit nested_exception(char const * msg, throwable const & ex):
        nested_exception(none_expr(), msg, ex) {}
    explicit nested_exception(format const & fmt, throwable const & ex):
        nested_exception(none_expr(), [=](formatter const &) { return fmt; }, ex) {}
    explicit nested_exception(sstream const & strm, throwable const & ex):
        nested_exception(none_expr(), strm, ex) {}
    virtual ~nested_exception() noexcept {}

    virtual optional<pos_info> get_pos() const override;
    virtual format pp(formatter const & fmt) const override;
    virtual throwable * clone() const override;
    virtual void rethrow() const override { throw *this; }
};

/* Similar to nested_exception but get_pos returns none
   even if nested exception has position information. */
class nested_exception_without_pos : public nested_exception {
    nested_exception_without_pos(pp_fn const & fn, throwable const & ex):
        nested_exception(none_expr(), fn, ex) {}
public:
    nested_exception_without_pos(char const * msg, throwable const & ex):
        nested_exception(msg, ex) {}
    virtual optional<pos_info> get_pos() const override { return optional<pos_info>(); }
    virtual throwable * clone() const override { return new nested_exception_without_pos(m_pp_fn, *m_exception); }
    virtual void rethrow() const override { throw *this; }
};

/** \brief Lean exception occurred when parsing file. */
class parser_nested_exception : public exception {
    std::shared_ptr<throwable>          m_exception;
public:
    parser_nested_exception(std::shared_ptr<throwable> const & ex): exception("parser exception"), m_exception(ex) {}
    virtual ~parser_nested_exception() {}
    virtual throwable * clone() const override { return new parser_nested_exception(m_exception); }
    virtual void rethrow() const override { throw *this; }
    virtual char const * what() const noexcept override { return m_exception->what(); }
    throwable const & get_exception() const { return *(m_exception.get()); }
};
}
