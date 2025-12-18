/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "kernel/local_ctx.h"
#include "runtime/interrupt.h"

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
    environment const & env() const { return m_env; }
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

class theorem_type_is_not_prop : public kernel_exception {
    name m_name;
    expr m_type;
public:
    theorem_type_is_not_prop(environment const & env, name const & n, expr const & type):
        kernel_exception(env), m_name(n), m_type(type) {}
    name const & get_decl_name() const { return m_name; }
    expr const & get_type() const { return m_type; }
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

/*
Helper function for interfacing C++ code with code written in Lean.
It executes closure `f` which produces an object_ref of type `A` and may throw
an `kernel_exception` or `exception`. Then, convert result into `Except Kernel.Exception T`
where `T` is the type of the lean objected represented by `A`.
We use the constructor `Kernel.Exception.other <msg>` to handle C++ `exception` objects which
are not `kernel_exception`.
*/
template<typename A>
object * catch_kernel_exceptions(std::function<A()> const & f) {
    try {
        A a = f();
        return mk_cnstr(1, a).steal();
    } catch (unknown_constant_exception & ex) {
        // 0  | unknownConstant  (env : Environment) (name : Name)
        return mk_cnstr(0, mk_cnstr(0, ex.env(), ex.get_name())).steal();
    } catch (already_declared_exception & ex) {
        // 1  | alreadyDeclared  (env : Environment) (name : Name)
        return mk_cnstr(0, mk_cnstr(1, ex.env(), ex.get_name())).steal();
    } catch (definition_type_mismatch_exception & ex) {
        // 2  | declTypeMismatch (env : Environment) (decl : Declaration) (givenType : Expr)
        return mk_cnstr(0, mk_cnstr(2, ex.env(), ex.get_declaration(), ex.get_given_type())).steal();
    } catch (declaration_has_metavars_exception & ex) {
        // 3  | declHasMVars     (env : Environment) (name : Name) (expr : Expr)
        return mk_cnstr(0, mk_cnstr(3, ex.env(), ex.get_decl_name(), ex.get_expr())).steal();
    } catch (declaration_has_free_vars_exception & ex) {
        // 4  | declHasFVars     (env : Environment) (name : Name) (expr : Expr)
        return mk_cnstr(0, mk_cnstr(4, ex.env(), ex.get_decl_name(), ex.get_expr())).steal();
    } catch (function_expected_exception & ex) {
        // 5  | funExpected      (env : Environment) (lctx : LocalContext) (expr : Expr)
        return mk_cnstr(0, mk_cnstr(5, ex.env(), ex.get_local_ctx(), ex.get_fn())).steal();
    } catch (type_expected_exception & ex) {
        // 6  | typeExpected     (env : Environment) (lctx : LocalContext) (expr : Expr)
        return mk_cnstr(0, mk_cnstr(6, ex.env(), ex.get_local_ctx(), ex.get_type())).steal();
    } catch (def_type_mismatch_exception & ex) {
        // 7  | letTypeMismatch  (env : Environment) (lctx : LocalContext) (name : Name) (givenType : Expr) (expectedType : Expr)
        return mk_cnstr(0, mk_cnstr(7, ex.env(), ex.get_local_ctx(), ex.get_name(), ex.get_given_type(), ex.get_expected_type())).steal();
    } catch (expr_type_mismatch_exception & ex) {
        // 8  | exprTypeMismatch (env : Environment) (lctx : LocalContext) (expr : Expr) (expectedType : Expr)
        return mk_cnstr(0, mk_cnstr(8, ex.env(), ex.get_local_ctx(), ex.get_expr(), ex.get_expected_type())).steal();
    } catch (app_type_mismatch_exception & ex) {
        // 9  | appTypeMismatch  (env : Environment) (lctx : LocalContext) (app : Expr) (funType : Expr) (argType : Expr)
        return mk_cnstr(0, mk_cnstr(9, ex.env(), ex.get_local_ctx(), ex.get_app(), ex.get_function_type(), ex.get_arg_type())).steal();
    } catch (invalid_proj_exception & ex) {
        // 10 | invalidProj      (env : Environment) (lctx : LocalContext) (proj : Expr)
        return mk_cnstr(0, mk_cnstr(10, ex.env(), ex.get_local_ctx(), ex.get_proj())).steal();
    } catch (theorem_type_is_not_prop & ex) {
        // 11 | thmTypeIsNotProp (env : Environment) (name : Name) (type : Expr)
        return mk_cnstr(0, mk_cnstr(11, ex.env(), ex.get_decl_name(), ex.get_type())).steal();
    } catch (exception & ex) {
        // 12 | other            (msg : String)
        return mk_cnstr(0, mk_cnstr(12, string_ref(ex.what()))).steal();
    } catch (heartbeat_exception & ex) {
        // 13 | deterministicTimeout
        return mk_cnstr(0, box(13)).steal();
    } catch (memory_exception & ex) {
        // 14 | excessiveMemory
        return mk_cnstr(0, box(14)).steal();
    } catch (stack_space_exception & ex) {
        // 15 | deepRecursion
        return mk_cnstr(0, box(15)).steal();
    } catch (interrupted & ex) {
        // 16 | interrupted
        return mk_cnstr(0, box(16)).steal();
    }
}
}
