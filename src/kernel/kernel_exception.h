/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "kernel/local_ctx.h"

namespace lean {
/** \brief Base class for all kernel exceptions. */
class kernel_exception : public exception {
protected:
    environment m_env;
public:
    kernel_exception(environment const & env):exception("kernel exception"), m_env(env) {}
    kernel_exception(environment const & env, char const * msg):exception(msg), m_env(env) {}
    kernel_exception(environment const & env, sstream const & strm):exception(strm), m_env(env) {}
    environment const & get_environment() const { return m_env; }
};

class unknown_constant_exception : public kernel_exception {
    name m_name;
public:
    unknown_constant_exception(environment const & env, name const & n):kernel_exception(env), m_name(n) {}
    name const & get_name() const { return m_name; }
};

class already_declared_exception : public kernel_exception {
    name m_name;
public:
    already_declared_exception(environment const & env, name const & n):kernel_exception(env), m_name(n) {}
    name const & get_name() const { return m_name; }
};

class definition_type_mismatch_exception : public kernel_exception {
    declaration m_decl;
    expr m_given_type;
public:
    definition_type_mismatch_exception(environment const & env, declaration const & decl, expr const & given_type):
        kernel_exception(env), m_decl(decl), m_given_type(given_type) {}
    declaration const & get_declaration() const { return m_decl; }
    expr const & get_given_type() const { return m_given_type; }
};

class declaration_has_metavars_exception : public kernel_exception {
    name m_name;
    expr m_expr;
public:
    declaration_has_metavars_exception(environment const & env, name const & n, expr const & e):
        kernel_exception(env), m_name(n), m_expr(e) {}
    name const & get_decl_name() const { return m_name; }
    expr const & get_expr() const { return m_expr; }
};

class declaration_has_free_vars_exception : public kernel_exception {
    name m_name;
    expr m_expr;
public:
    declaration_has_free_vars_exception(environment const & env, name const & n, expr const & e):
        kernel_exception(env), m_name(n), m_expr(e) {}
    name const & get_decl_name() const { return m_name; }
    expr const & get_expr() const { return m_expr; }
};

class kernel_exception_with_lctx : public kernel_exception {
    local_ctx m_lctx;
public:
    kernel_exception_with_lctx(environment const & env, local_ctx const & lctx):
        kernel_exception(env), m_lctx(lctx) {}
    local_ctx const & get_local_ctx() const { return m_lctx; }
};

class function_expected_exception : public kernel_exception_with_lctx {
    expr m_fn;
public:
    function_expected_exception(environment const & env, local_ctx const & lctx, expr const & fn):
        kernel_exception_with_lctx(env, lctx), m_fn(fn) {}
    expr const & get_fn() const { return m_fn; }
};

class type_expected_exception : public kernel_exception_with_lctx {
    expr m_type;
public:
    type_expected_exception(environment const & env, local_ctx const & lctx, expr const & type):
        kernel_exception_with_lctx(env, lctx), m_type(type) {}
    expr const & get_type() const { return m_type; }
};

class type_mismatch_exception : public kernel_exception_with_lctx {
    expr m_given_type;
    expr m_expected_type;
public:
    type_mismatch_exception(environment const & env, local_ctx const & lctx, expr const & given_type, expr const & expected_type):
        kernel_exception_with_lctx(env, lctx), m_given_type(given_type), m_expected_type(expected_type) {}
    expr const & get_given_type() const { return m_given_type; }
    expr const & get_expected_type() const { return m_expected_type; }
};

class def_type_mismatch_exception : public type_mismatch_exception {
    name m_name;
public:
    def_type_mismatch_exception(environment const & env, local_ctx const & lctx, name const & n, expr const & given_type, expr const & expected_type):
        type_mismatch_exception(env, lctx, given_type, expected_type), m_name(n) {}
    name const & get_name() const { return m_name; }
};

class expr_type_mismatch_exception : public kernel_exception_with_lctx {
    expr m_expr;
    expr m_expected_type;
public:
    expr_type_mismatch_exception(environment const & env, local_ctx const & lctx, expr const & e, expr const & expected_type):
        kernel_exception_with_lctx(env, lctx), m_expr(e), m_expected_type(expected_type) {}
    expr const & get_expr() const { return m_expr; }
    expr const & get_expected_type() const { return m_expected_type; }
};

class app_type_mismatch_exception : public kernel_exception_with_lctx {
    expr m_app;
    expr m_function_type;
    expr m_arg_type;
public:
    app_type_mismatch_exception(environment const & env, local_ctx const & lctx, expr const & app,
            expr const & function_type, expr const & arg_type):
        kernel_exception_with_lctx(env, lctx), m_app(app), m_function_type(function_type), m_arg_type(arg_type) {}
    expr const & get_app() const { return m_app; }
    expr const & get_function_type() const { return m_function_type; }
    expr const & get_arg_type() const { return m_arg_type; }
};

class invalid_proj_exception : public kernel_exception_with_lctx {
    expr m_proj;
public:
    invalid_proj_exception(environment const & env, local_ctx const & lctx, expr const & proj):
        kernel_exception_with_lctx(env, lctx), m_proj(proj) {}
    expr const & get_proj() const { return m_proj; }
};
}
