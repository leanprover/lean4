/*
Copyright (c) 2013-14 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include "util/name_generator.h"
#include "util/name_set.h"
#include "kernel/environment.h"
#include "kernel/constraint.h"
#include "kernel/converter.h"

namespace lean {
class constraint_handler {
public:
    virtual ~constraint_handler() {}
    virtual void add_cnstr(constraint const & c) = 0;
};

/** \brief This handler always throw an exception (\c no_constraints_allowed_exception) when \c add_cnstr is invoked. */
class no_constraint_handler : public constraint_handler {
public:
    virtual void add_cnstr(constraint const & c);
};

/** \brief Exception used in \c no_constraint_handler. */
class no_constraints_allowed_exception : public exception {
public:
    no_constraints_allowed_exception();
    virtual exception * clone() const;
    virtual void rethrow() const;
};

/**
   \brief Lean Type Checker. It can also be used to infer types, check whether a
   type \c A is convertible to a type \c B, etc.

   The type checker produces constraints, and they are sent to the constraint handler.
*/
class type_checker {
    struct imp;
    std::unique_ptr<imp> m_ptr;
public:
    /**
       \brief Create a type checker for the given environment. The auxiliary names created by this
       type checker are based on the given name generator.

       memoize: if true, then inferred types are memoized/cached
    */
    type_checker(environment const & env, name_generator const & g, constraint_handler & h, std::unique_ptr<converter> && conv,
                 bool memoize = true);
    type_checker(environment const & env, name_generator const & g, constraint_handler & h, bool memoize = true):
        type_checker(env, g, h, mk_default_converter(env), memoize) {}
    /**
       \brief Similar to the previous constructor, but if a method tries to create a constraint, then an
       exception is thrown.
    */
    type_checker(environment const & env, name_generator const & g, std::unique_ptr<converter> && conv, bool memoize = true);
    type_checker(environment const & env, name_generator const & g, bool memoize = true):
        type_checker(env, g, mk_default_converter(env), memoize) {}
    type_checker(environment const & env);
    ~type_checker();

    /**
       \brief Return the type of \c t.

       It does not check whether the input expression is type correct or not.
       The contract is: IF the input expression is type correct, then the inferred
       type is correct.
       Throw an exception if a type error is found.

       The result is meaningful only if the constraints sent to the
       constraint handler can be solved.
   */
    expr infer(expr const & t);

    /**
       \brief Type check the given expression, and return the type of \c t.
       Throw an exception if a type error is found.

       The result is meaningful only if the constraints sent to the
       constraint handler can be solved.
    */
    expr check(expr const & t, level_param_names const & ps = level_param_names());
    /** \brief Return true iff t is definitionally equal to s. */
    bool is_def_eq(expr const & t, expr const & s);
    /** \brief Return true iff t is a proposition. */
    bool is_prop(expr const & t);
    /** \brief Return the weak head normal form of \c t. */
    expr whnf(expr const & t);
    /** \brief Return a Pi if \c t is convertible to a Pi type. Throw an exception otherwise. */
    expr ensure_pi(expr const & t);
    /** \brief Return a Sort if \c t is convertible to Sort. Throw an exception otherwise. */
    expr ensure_sort(expr const & t);
};

/**
   \brief Type check the given definition, and return a certified definition if it is type correct.
   Throw an exception if the definition is type incorrect.
*/
certified_definition check(environment const & env, definition const & d,
                           name_generator const & g, name_set const & extra_opaque = name_set(), bool memoize = true);
certified_definition check(environment const & env, definition const & d, name_set const & extra_opaque = name_set(), bool memoize = true);
}
