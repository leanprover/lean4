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
   \brief Given pi == (Pi x : A, B x), return (B a)

   \pre is_pi(pi)
   \pre type of a is A
*/
expr pi_body_at(expr const & pi, expr const & a);

/**
   \brief Lean Type Checker. It can also be used to infer types, universes and check whether a
   type \c A is convertible to a type \c B.
*/
class type_checker {
    class imp;
    std::unique_ptr<imp> m_ptr;
public:
    type_checker(ro_environment const & env, bool infer_only = false);
    ~type_checker();

    /**
       \brief Return the type of \c e in the context \c ctx.

       It does not check whether the input expression is type correct or not.
       The contract is: IF the input expression is type correct, then the inferred
       type is correct.

       \remark This method throws an exception if \c e is not type correct.

       \remark If \c menv is not none, then \c e may contain metavariables.
       New metavariables and unification constraints may be created by the type checker.
       The new unification constraints are stored in \c new_constraints.
    */
    expr infer_type(expr const & e, context const & ctx, optional<metavar_env> const & menv, buffer<unification_constraint> * new_constraints);
    expr infer_type(expr const & e, context const & ctx, metavar_env const & menv, buffer<unification_constraint> & new_constraints);
    expr infer_type(expr const & e, context const & ctx, metavar_env const & menv);

    /**
        \brief Return the type of \c e in the context \c ctx.

        \remark This method throws an exception if \c e is not type
        correct, or if \c e contains metavariables.
    */
    expr infer_type(expr const & e, context const & ctx = context());

    /**
       \brief Type check the given expression, and return the type of \c e in the context \c ctx.

       \remark This method throws an exception if \c e is not type correct.

       \remark If \c menv is not none, then \c e may contain metavariables.
       New metavariables and unification constraints may be created by the type checker.
       The new unification constraints are stored in \c new_constraints.
    */
    expr check(expr const & e, context const & ctx, optional<metavar_env> const & menv, buffer<unification_constraint> * new_constraints);
    expr check(expr const & e, context const & ctx, metavar_env const & menv, buffer<unification_constraint> & new_constraints);
    expr check(expr const & e, context const & ctx, metavar_env const & menv);

    /**
        \brief Type check the given expression, and return the type of \c e in the context \c ctx.

        \remark This method throws an exception if \c e is not type
        correct, or if \c e contains metavariables.
    */
    expr check(expr const & e, context const & ctx = context());

    /** \brief Throw an exception if \c e is not a type in the context \c ctx. */
    void check_type(expr const & e, context const & ctx = context());

    /** \brief Return true iff \c t1 is convertible to \c t2 in the context \c ctx. */
    bool is_convertible(expr const & t1, expr const & t2, context const & ctx = context());

    /** \brief Return true iff \c e is a proposition (i.e., it has type Bool) */
    bool is_proposition(expr const & e, context const & ctx, optional<metavar_env> const & menv);
    bool is_proposition(expr const & e, context const & ctx, metavar_env const & menv);
    bool is_proposition(expr const & e, context const & ctx = context());

    /** \brief Return true iff \c e is a proposition or is a Pi s.t. the range is a flex_proposition */
    bool is_flex_proposition(expr e, context ctx, optional<metavar_env> const & menv);
    bool is_flex_proposition(expr const & e, context const & ctx, metavar_env const & menv);
    bool is_flex_proposition(expr const & e, context const & ctx = context());

    /** \brief Return a Pi if \c e is convertible to Pi. Throw an exception otherwise. */
    expr ensure_pi(expr const & e, context const & ctx = context());

    /** \brief Reset internal caches */
    void clear();

    /** \brief Return reference to the normalizer used by this type checker. */
    normalizer & get_normalizer();
};
class type_inferer : public type_checker {
public:
    type_inferer(ro_environment const & env):type_checker(env, true) {}
    expr operator()(expr const & e, context const & ctx, optional<metavar_env> const & menv, buffer<unification_constraint> * new_constraints) {
        return infer_type(e, ctx, menv, new_constraints);
    }
    expr operator()(expr const & e, context const & ctx, metavar_env const & menv, buffer<unification_constraint> & new_constraints) {
        return infer_type(e, ctx, menv, new_constraints);
    }
    expr operator()(expr const & e, context const & ctx, metavar_env const & menv) {
        return infer_type(e, ctx, menv);
    }
    expr operator()(expr const & e, context const & ctx = context()) {
        return infer_type(e, ctx);
    }
};
expr type_check(expr const & e, ro_environment const & env, context const & ctx = context());
bool is_convertible(expr const & t1, expr const & t2, ro_environment const & env, context const & ctx = context());
bool is_proposition(expr const & e, ro_environment const & env, context const & ctx, optional<metavar_env> const & menv);
bool is_proposition(expr const & e, ro_environment const & env, context const & ctx, metavar_env const & menv);
bool is_proposition(expr const & e, ro_environment const & env, context const & ctx = context());
}
