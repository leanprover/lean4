/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <string>
#include "util/sstream.h"
#include "kernel/scope_pos_info_provider.h"
#include "kernel/kernel_exception.h"

namespace lean {
format kernel_exception::pp(formatter const &) const { return format(what()); }

class generic_kernel_exception : public kernel_exception {
protected:
    optional<pos_info> m_pos;
    pp_fn              m_pp_fn;
public:
    generic_kernel_exception(environment const & env, char const * msg, optional<pos_info> const & p, pp_fn const & fn):
        kernel_exception(env, msg), m_pos(p), m_pp_fn(fn) {}
    generic_kernel_exception(environment const & env, char const * msg, optional<expr> const & m, pp_fn const & fn):
            generic_kernel_exception(env, msg, get_pos_info(m), fn) {}
    virtual ~generic_kernel_exception() noexcept {}
    virtual optional<pos_info> get_pos() const override { return m_pos; }
    virtual format pp(formatter const & fmt) const override { return m_pp_fn(fmt); }
    virtual throwable * clone() const override { return new generic_kernel_exception(m_env, m_msg.c_str(), m_pos, m_pp_fn); }
    virtual void rethrow() const override { throw *this; }
};

[[ noreturn ]] void throw_kernel_exception(environment const & env, char const * msg, optional<expr> const & m) {
    std::string msg_str = msg;
    throw generic_kernel_exception(env, msg, m, [=](formatter const &) { return format(msg_str); });
}

[[ noreturn ]] void throw_kernel_exception(environment const & env, sstream const & strm, optional<expr> const & m) {
    throw_kernel_exception(env, strm.str().c_str(), m);
}

[[ noreturn ]] void throw_kernel_exception(environment const & env, char const * msg, expr const & m) {
    throw_kernel_exception(env, msg, some_expr(m));
}

[[ noreturn ]] void throw_kernel_exception(environment const & env, sstream const & strm, expr const & m) {
    throw_kernel_exception(env, strm, some_expr(m));
}

[[ noreturn ]] void throw_kernel_exception(environment const & env, char const * msg, optional<expr> const & m, pp_fn const & fn) {
    throw generic_kernel_exception(env, msg, m, fn);
}

[[ noreturn ]] void throw_kernel_exception(environment const & env, optional<expr> const & m, pp_fn const & fn) {
    throw generic_kernel_exception(env, "kernel exception", m, fn);
}

[[ noreturn ]] void throw_kernel_exception(environment const & env, char const * msg, expr const & m, pp_fn const & fn) {
    throw_kernel_exception(env, msg, some_expr(m), fn);
}

[[ noreturn ]] void throw_kernel_exception(environment const & env, expr const & m, pp_fn const & fn) {
    throw_kernel_exception(env, some_expr(m), fn);
}

[[ noreturn ]] void throw_unknown_declaration(environment const & env, name const & n) {
    throw_kernel_exception(env, sstream() << "unknown declaration '" << n << "'");
}

[[ noreturn ]] void throw_already_declared(environment const & env, name const & n) {
    throw_kernel_exception(env, sstream() << "invalid object declaration, environment already has an object named '" << n << "'");
}
}
