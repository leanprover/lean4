/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "elaborator.h"
#include "kernel_exception.h"

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
    unsigned m_arg_pos;
public:
    unification_app_mismatch_exception(elaborator const & elb, context const & ctx, expr const & s, unsigned pos):elaborator_exception(elb, ctx, s), m_arg_pos(pos) {}
    unsigned get_arg_pos() const { return m_arg_pos; }
    virtual char const * what() const noexcept { return "application type mismatch during term elaboration"; }
};

class unification_type_mismatch_exception : public elaborator_exception {
public:
    unification_type_mismatch_exception(elaborator const & elb, context const & ctx, expr const & s):elaborator_exception(elb, ctx, s) {}
    virtual char const * what() const noexcept { return "type mismatch during term elaboration"; }
};
}
