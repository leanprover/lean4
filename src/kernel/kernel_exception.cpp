/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <string>
#include "util/sstream.h"
#include "kernel/kernel_exception.h"

namespace lean {
format kernel_exception::pp(formatter const &, options const &) const { return format(what()); }

class generic_kernel_exception : public kernel_exception {
protected:
    optional<expr> m_main_expr;
    pp_fn          m_pp_fn;
public:
    generic_kernel_exception(ro_environment const & env, char const * msg, optional<expr> const & m, pp_fn const & fn):
        kernel_exception(env, msg),
        m_main_expr(m),
        m_pp_fn(fn) {}
    virtual ~generic_kernel_exception() noexcept {}
    virtual optional<expr> get_main_expr() const { return m_main_expr; }
    virtual format pp(formatter const & fmt, options const & opts) const { return m_pp_fn(fmt, opts); }
    virtual exception * clone() const { return new generic_kernel_exception(m_env, m_msg.c_str(), m_main_expr, m_pp_fn); }
    virtual void rethrow() const { throw *this; }
};

[[ noreturn ]] void throw_kernel_exception(ro_environment const & env, char const * msg, optional<expr> const & m) {
    std::string msg_str = msg;
    throw generic_kernel_exception(env, msg, m, [=](formatter const &, options const &) { return format(msg); });
}

[[ noreturn ]] void throw_kernel_exception(ro_environment const & env, sstream const & strm, optional<expr> const & m) {
    throw_kernel_exception(env, strm.str().c_str(), m);
}

[[ noreturn ]] void throw_kernel_exception(ro_environment const & env, char const * msg, pp_fn const & fn,
                                           optional<expr> const & m) {
    throw generic_kernel_exception(env, msg, m, fn);
}

[[ noreturn ]] void throw_kernel_exception(ro_environment const & env, pp_fn const & fn, optional<expr> const & m) {
    throw generic_kernel_exception(env, "kernel exception", m, fn);
}

[[ noreturn ]] void throw_unknown_object(ro_environment const & env, name const & n) {
    throw_kernel_exception(env, sstream() << "unknown object '" << n << "'");
}

[[ noreturn ]] void throw_already_declared(ro_environment const & env, name const & n) {
    throw_kernel_exception(env, sstream() << "invalid object declaration, environment already has an object named '" << n << "'");
}

[[ noreturn ]] void throw_read_only_environment(ro_environment const & env) {
    throw_kernel_exception(env, "environment cannot be updated because it has children environments");
}
}
