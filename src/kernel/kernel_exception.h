/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "kernel/ext_exception.h"
#include "kernel/scope_pos_info_provider.h"

namespace lean {
class environment;
/** \brief Base class for all kernel exceptions. */
class kernel_exception : public ext_exception {
protected:
    environment m_env;
public:
    kernel_exception(environment const & env):m_env(env) {}
    kernel_exception(environment const & env, char const * msg):ext_exception(msg), m_env(env) {}
    kernel_exception(environment const & env, sstream const & strm):ext_exception(strm), m_env(env) {}
    environment const & get_environment() const { return m_env; }
    virtual format pp(formatter const & fmt) const override;
    virtual throwable * clone() const override { return new kernel_exception(m_env, m_msg.c_str()); }
    virtual void rethrow() const override { throw *this; }
};

class definition_type_mismatch_exception : public kernel_exception {
    declaration m_decl;
    expr m_given_type;
public:
    definition_type_mismatch_exception(environment const & env, declaration const & decl, expr const & given_type):
            kernel_exception(env), m_decl(decl), m_given_type(given_type) {}
    expr const & get_given_type() const { return m_given_type; }
    virtual optional<pos_info> get_pos() const override { return get_pos_info(m_decl.get_value()); }
    virtual format pp(formatter const & fmt) const override;
    virtual throwable * clone() const override { return new definition_type_mismatch_exception(m_env, m_decl, m_given_type); }
    virtual void rethrow() const override { throw *this; }
};

[[ noreturn ]] void throw_kernel_exception(environment const & env, char const * msg, optional<expr> const & m = none_expr());
[[ noreturn ]] void throw_kernel_exception(environment const & env, sstream const & strm, optional<expr> const & m = none_expr());
[[ noreturn ]] void throw_kernel_exception(environment const & env, char const * msg, expr const & m);
[[ noreturn ]] void throw_kernel_exception(environment const & env, sstream const & strm, expr const & m);
[[ noreturn ]] void throw_kernel_exception(environment const & env, char const * msg, optional<expr> const & m, pp_fn const & fn);
[[ noreturn ]] void throw_kernel_exception(environment const & env, optional<expr> const & m, pp_fn const & fn);
[[ noreturn ]] void throw_kernel_exception(environment const & env, char const * msg, expr const & m, pp_fn const & fn);
[[ noreturn ]] void throw_kernel_exception(environment const & env, expr const & m, pp_fn const & fn);
[[ noreturn ]] void throw_unknown_declaration(environment const & env, name const & n);
[[ noreturn ]] void throw_already_declared(environment const & env, name const & n);
}
