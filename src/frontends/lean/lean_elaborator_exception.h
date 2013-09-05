/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "lean_elaborator.h"
#include "kernel_exception.h"
#include "state.h"

namespace lean {
/**
    \brief Base class for elaborator exceptions.

    \remark We reuse kernel exceptions to sign type errors during
    elaboration. Perhaps we should wrap them as elaborator exceptions.
*/
class elaborator_exception : public exception {
protected:
    elaborator m_elb;
    context    m_context;
    expr       m_expr;
public:
    elaborator_exception(elaborator const & elb, context const & ctx, expr const & e):m_elb(elb), m_context(ctx), m_expr(e) {}
    virtual ~elaborator_exception() noexcept {}
    elaborator const & get_elaborator() const { return m_elb; }
    expr const & get_expr() const { return m_expr; }
    context const & get_context() const { return m_context; }
    virtual format pp(formatter const & fmt, options const & opts) const;
};

class invalid_placeholder_exception : public elaborator_exception {
public:
    invalid_placeholder_exception(elaborator const & elb, context const & ctx, expr const & e):elaborator_exception(elb, ctx, e) {}
    virtual char const * what() const noexcept { return "invalid placeholder occurrence, placeholder cannot be used as application head"; }
};

class unsolved_placeholder_exception : public elaborator_exception {
public:
    unsolved_placeholder_exception(elaborator const & elb, context const & ctx, expr const & e):elaborator_exception(elb, ctx, e) {}
    virtual char const * what() const noexcept { return "unsolved placeholder"; }
};

class unification_app_mismatch_exception : public elaborator_exception {
    std::vector<expr> m_args;
    std::vector<expr> m_types;
public:
    unification_app_mismatch_exception(elaborator const & elb, context const & ctx, expr const & s,
                                       std::vector<expr> const & args, std::vector<expr> const & types):
        elaborator_exception(elb, ctx, s),
        m_args(args),
        m_types(types) {}
    virtual ~unification_app_mismatch_exception() {}
    std::vector<expr> const & get_args() const { return m_args; }
    std::vector<expr> const & get_types() const { return m_types; }
    virtual char const * what() const noexcept { return "application type mismatch during term elaboration"; }
    virtual format pp(formatter const & fmt, options const & opts) const;
};

class unification_type_mismatch_exception : public elaborator_exception {
    expr m_processed_expr;
    expr m_expected_type;
    expr m_given_type;
public:
    unification_type_mismatch_exception(elaborator const & elb, context const & ctx, expr const & s,
                                        expr const & processed, expr const & expected, expr const & given):
        elaborator_exception(elb, ctx, s), m_processed_expr(processed), m_expected_type(expected), m_given_type(given) {}
    virtual ~unification_type_mismatch_exception() {}
    expr const & get_processed_expr() const { return m_processed_expr; }
    expr const & get_expected_type() const { return m_expected_type; }
    expr const & get_given_type() const { return m_given_type; }
    virtual char const * what() const noexcept { return "type mismatch during term elaboration"; }
    virtual format pp(formatter const & fmt, options const & opts) const;
};

class overload_exception : public elaborator_exception {
    std::vector<expr> m_fs;
    std::vector<expr> m_f_types;
    std::vector<expr> m_args;
    std::vector<expr> m_arg_types;
public:
    overload_exception(elaborator const & elb, context const & ctx, expr const & s,
                          unsigned num_fs, expr const * fs, expr const * ftypes,
                          unsigned num_args, expr const * args, expr const * argtypes):
        elaborator_exception(elb, ctx, s),
        m_fs(fs, fs + num_fs),
        m_f_types(ftypes, ftypes + num_fs),
        m_args(args, args + num_args),
        m_arg_types(argtypes, argtypes + num_args) {
    }
    virtual ~overload_exception() {}
    std::vector<expr> const & get_fs() const { return m_fs; }
    std::vector<expr> const & get_f_types() const { return m_f_types; }
    std::vector<expr> const & get_args() const { return m_args; }
    std::vector<expr> const & get_arg_types() const { return m_arg_types; }
    virtual format pp(formatter const & fmt, options const & opts) const;
};

class no_overload_exception : public overload_exception {
public:
    no_overload_exception(elaborator const & elb, context const & ctx, expr const & s,
                          unsigned num_fs, expr const * fs, expr const * ftypes,
                          unsigned num_args, expr const * args, expr const * argtypes):
        overload_exception(elb, ctx, s, num_fs, fs, ftypes, num_args, args, argtypes) {}
    virtual char const * what() const noexcept { return "application type mismatch, none of the overloads can be used"; }
};

class ambiguous_overload_exception : public overload_exception {
public:
    ambiguous_overload_exception(elaborator const & elb, context const & ctx, expr const & s,
                                 unsigned num_fs, expr const * fs, expr const * ftypes,
                                 unsigned num_args, expr const * args, expr const * argtypes):
        overload_exception(elb, ctx, s, num_fs, fs, ftypes, num_args, args, argtypes) {}
    virtual char const * what() const noexcept { return "ambiguous overloads"; }
};

regular const & operator<<(regular const & out, elaborator_exception const & ex);
diagnostic const & operator<<(diagnostic const & out, elaborator_exception const & ex);
}
