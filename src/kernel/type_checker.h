/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "kernel/expr.h"
#include "kernel/context.h"
#include "kernel/unification_constraint.h"
#include "kernel/metavar.h"

namespace lean {
class environment;
class normalizer;
/**
   \brief Lean Type Checker. It can also be used to infer types, universes and check whether a
   type \c A is convertible to a type \c B.
*/
class type_checker {
    class imp;
    std::unique_ptr<imp> m_ptr;
public:
    type_checker(environment const & env);
    ~type_checker();

    /**
       \brief Return the type of \c e in the context \c ctx.

       \remark This method throws an exception if \c e is not type correct.

       \remark If \c menv is not nullptr, then \c e may contain metavariables.
       New metavariables and unification constraints may be created by the type checker.
       The new unification constraints are stored in \c new_constraints.
    */
    expr infer_type(expr const & e, context const & ctx, metavar_env * menv, buffer<unification_constraint> * new_constraints);

    /**
        \brief Return the type of \c e in the context \c ctx.

        \remark This method throws an exception if \c e is not type
        correct, or if \c e contains metavariables.
    */
    expr infer_type(expr const & e, context const & ctx = context());

    /** \brief Throw an exception if \c e is not type correct in the context \c ctx. */
    void check(expr const & e, context const & ctx = context()) { infer_type(e, ctx); }

    /** \brief Throw an exception if \c e is not a type in the context \c ctx. */
    void check_type(expr const & e, context const & ctx = context());

    /** \brief Return true iff \c t1 is convertible to \c t2 in the context \c ctx. */
    bool is_convertible(expr const & t1, expr const & t2, context const & ctx = context());

    /** \brief Reset internal caches */
    void clear();

    /** \brief Return reference to the normalizer used by this type checker. */
    normalizer & get_normalizer();
};

expr infer_type(expr const & e, environment const & env, context const & ctx = context());
bool is_convertible(expr const & t1, expr const & t2, environment const & env, context const & ctx = context());
}
