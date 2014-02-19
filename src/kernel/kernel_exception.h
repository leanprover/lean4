/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include "util/exception.h"
#include "util/sexpr/options.h"
#include "kernel/context.h"
#include "kernel/environment.h"
#include "kernel/formatter.h"

namespace lean {
class environment;
/** \brief Base class for all kernel exceptions. */
class kernel_exception : public exception {
protected:
    ro_environment m_env;
public:
    kernel_exception(ro_environment const & env):m_env(env) {}
    kernel_exception(ro_environment const & env, char const * msg):exception(msg), m_env(env) {}
    kernel_exception(ro_environment const & env, sstream const & strm):exception(strm), m_env(env) {}
    virtual ~kernel_exception() noexcept {}
    ro_environment const & get_environment() const { return m_env; }
    /**
        \brief Return a reference (if available) to the main expression associated with this exception.
        This information is used to provide better error messages.
    */
    virtual optional<expr> get_main_expr() const { return none_expr(); }
    virtual format pp(formatter const & fmt, options const & opts) const;
    virtual exception * clone() const { return new kernel_exception(m_env, m_msg.c_str()); }
    virtual void rethrow() const { throw *this; }
};

[[ noreturn ]] void throw_kernel_exception(ro_environment const & env, char const * msg, optional<expr> const & m = none_expr());
[[ noreturn ]] void throw_kernel_exception(ro_environment const & env, sstream const & strm,
                                           optional<expr> const & m = none_expr());
[[ noreturn ]] void throw_kernel_exception(ro_environment const & env, char const * msg,
                                           pp_fn const & fn, optional<expr> const & m = none_expr());
[[ noreturn ]] void throw_kernel_exception(ro_environment const & env, pp_fn const & fn, optional<expr> const & m = none_expr());

[[ noreturn ]] void throw_unknown_object(ro_environment const & env, name const & n);
[[ noreturn ]] void throw_already_declared(ro_environment const & env, name const & n);
[[ noreturn ]] void throw_read_only_environment(ro_environment const & env);



#if 0
/** \brief Base class for type checking related exceptions. */
class type_checker_exception : public kernel_exception {
public:
    type_checker_exception(ro_environment const & env):kernel_exception(env) {}
    virtual exception * clone() const { return new type_checker_exception(m_env); }
    virtual void rethrow() const { throw *this; }
};

/** \brief Exception for objects that do not have types associated with them */
class has_no_type_exception : public type_checker_exception {
    expr m_const;
public:
    has_no_type_exception(ro_environment const & env, expr const & c):type_checker_exception(env), m_const(c) {}
    virtual ~has_no_type_exception() {}
    virtual optional<expr> get_main_expr() const { return some_expr(m_const); }
    virtual char const * what() const noexcept { return "object does not have a type associated with it"; }
    virtual format pp(formatter const & fmt, options const & opts) const;
    virtual exception * clone() const { return new has_no_type_exception(m_env, m_const); }
    virtual void rethrow() const { throw *this; }
};

/**
    \brief Exception used to report an application argument type
    mismatch.

    Explanation:
    In the environment get_environment() and local context
    get_context(), the argument get_arg_pos() of the application
    get_application() has type get_given_type(), but it is expected to
    have type get_expected_type().
*/
class app_type_mismatch_exception : public type_checker_exception {
    context           m_context;
    expr              m_app;
    unsigned          m_arg_pos;
    std::vector<expr> m_arg_types;
public:
    app_type_mismatch_exception(ro_environment const & env, context const & ctx, expr const & app, unsigned arg_pos,
                                unsigned num, expr const * arg_types):
        type_checker_exception(env), m_context(ctx), m_app(app), m_arg_pos(arg_pos), m_arg_types(arg_types, arg_types+num) {}
    virtual ~app_type_mismatch_exception() {}
    context const & get_context() const { return m_context; }
    expr const & get_application() const { return m_app; }
    virtual optional<expr> get_main_expr() const { return some_expr(get_application()); }
    unsigned get_arg_pos() const { return m_arg_pos; }
    std::vector<expr> const & get_arg_types() const { return m_arg_types; }
    virtual char const * what() const noexcept { return "application argument type mismatch"; }
    virtual format pp(formatter const & fmt, options const & opts) const;
    virtual exception * clone() const { return new app_type_mismatch_exception(m_env, m_context, m_app, m_arg_pos, m_arg_types.size(), m_arg_types.data()); }
    virtual void rethrow() const { throw *this; }
};

class pair_type_mismatch_exception : public type_checker_exception {
    context     m_context;
    expr        m_pair;
    bool        m_first;
    expr        m_arg_type;
    expr        m_sig_type;
public:
    pair_type_mismatch_exception(ro_environment const & env, context const & ctx, expr const & pair,
                                 bool first, expr const & arg_type, expr const & sig_type):
        type_checker_exception(env), m_context(ctx), m_pair(pair), m_first(first), m_arg_type(arg_type), m_sig_type(sig_type) {}
    virtual ~pair_type_mismatch_exception() {}
    context const & get_context() const { return m_context; }
    expr const & get_pair() const { return m_pair; }
    virtual optional<expr> get_main_expr() const { return some_expr(get_pair()); }
    bool first() const { return m_first; }
    virtual char const * what() const noexcept { return "pair argument type mismatch"; }
    virtual format pp(formatter const & fmt, options const & opts) const;
    virtual exception * clone() const { return new pair_type_mismatch_exception(m_env, m_context, m_pair, m_first, m_arg_type, m_sig_type); }
    virtual void rethrow() const { throw *this; }
};

/**
   \brief Exception used to report than an expression that is not a
   function (pair) is being used as a function (pair)

   Explanation:
   In the environment get_environment() and local context
   get_context(), the expression get_expr() is expected to be a function (pair).
*/
class abstraction_expected_exception : public type_checker_exception {
protected:
    context m_context;
    expr    m_expr;
public:
    abstraction_expected_exception(ro_environment const & env, context const & ctx, expr const & e):
        type_checker_exception(env), m_context(ctx), m_expr(e) {}
    virtual ~abstraction_expected_exception() {}
    context const & get_context() const { return m_context; }
    expr const & get_expr() const { return m_expr; }
    virtual optional<expr> get_main_expr() const { return some_expr(get_expr()); }
    virtual format pp(formatter const & fmt, options const & opts) const;
};

class function_expected_exception : public abstraction_expected_exception {
public:
    function_expected_exception(ro_environment const & env, context const & ctx, expr const & e):
        abstraction_expected_exception(env, ctx, e) {}
    virtual char const * what() const noexcept { return "function expected"; }
    virtual exception * clone() const { return new function_expected_exception(m_env, m_context, m_expr); }
    virtual void rethrow() const { throw *this; }
};

class pair_expected_exception : public abstraction_expected_exception {
public:
    pair_expected_exception(ro_environment const & env, context const & ctx, expr const & e):
        abstraction_expected_exception(env, ctx, e) {}
    virtual char const * what() const noexcept { return "pair expected"; }
    virtual exception * clone() const { return new pair_expected_exception(m_env, m_context, m_expr); }
    virtual void rethrow() const { throw *this; }
};

/**
   \brief Exception used to report than an expression that is not a
   type is being used where a type is expected.

   Explanation:
   In the environment get_environment() and local context
   get_context(), the expression get_expr() is expected to be a type.
*/
class type_expected_exception : public type_checker_exception {
    context m_context;
    expr    m_expr;
public:
    type_expected_exception(ro_environment const & env, context const & ctx, expr const & e):
        type_checker_exception(env), m_context(ctx), m_expr(e) {}
    virtual ~type_expected_exception() {}
    context const & get_context() const { return m_context; }
    expr const & get_expr() const { return m_expr; }
    virtual optional<expr> get_main_expr() const { return some_expr(get_expr()); }
    virtual char const * what() const noexcept { return "type expected"; }
    virtual format pp(formatter const & fmt, options const & opts) const;
    virtual exception * clone() const { return new type_expected_exception(m_env, m_context, m_expr); }
    virtual void rethrow() const { throw *this; }
};

/**
    \brief Exception used to report a definition type mismatch.

    Explanation:
    In the environment get_environment(), the declaration with name
    get_name(), type get_type() and value get_value() is incorrect
    because the value has type get_value_type() and it not matches
    the given type get_type().

    This exception is also used to sign declaration mismatches in
    let declarations.
*/
class def_type_mismatch_exception : public type_checker_exception {
    context m_context;
    name    m_name;
    expr    m_type;
    expr    m_value;
    expr    m_value_type;
public:
    def_type_mismatch_exception(ro_environment const & env, context const & ctx, name const & n, expr const & type, expr const & val, expr const & val_type):
        type_checker_exception(env), m_context(ctx), m_name(n), m_type(type), m_value(val), m_value_type(val_type) {}
    def_type_mismatch_exception(ro_environment const & env, name const & n, expr const & type, expr const & val, expr const & val_type):
        type_checker_exception(env), m_name(n), m_type(type), m_value(val), m_value_type(val_type) {}
    virtual ~def_type_mismatch_exception() {}
    name const & get_name() const { return m_name; }
    context const & get_context() const { return m_context; }
    expr const & get_type() const { return m_type; }
    expr const & get_value() const { return m_value; }
    expr const & get_value_type() const { return m_value_type; }
    virtual optional<expr> get_main_expr() const { return some_expr(m_value); }
    virtual char const * what() const noexcept { return "definition type mismatch"; }
    virtual format pp(formatter const & fmt, options const & opts) const;
    virtual exception * clone() const { return new def_type_mismatch_exception(m_env, m_context, m_name, m_type, m_value, m_value_type); }
    virtual void rethrow() const { throw *this; }
};

/**
   \brief Unexpected metavariable occurrence
*/
class unexpected_metavar_occurrence : public kernel_exception {
    expr m_expr;
public:
    unexpected_metavar_occurrence(ro_environment const & env, expr const & e):kernel_exception(env), m_expr(e) {}
    virtual ~unexpected_metavar_occurrence() {}
    virtual char const * what() const noexcept { return "unexpected metavariable occurrence"; }
    virtual optional<expr> get_main_expr() const { return some_expr(m_expr); }
    virtual exception * clone() const { return new unexpected_metavar_occurrence(m_env, m_expr); }
    virtual void rethrow() const { throw *this; }
};
#endif
}
