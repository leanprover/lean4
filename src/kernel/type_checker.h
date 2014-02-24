/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include "util/name_generator.h"
#include "kernel/expr.h"
#include "kernel/constraint.h"

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

   Remark: several methods take a \c name_generator as argument. The name generator is used
   for creating fresh metavariables and local variables.

   Remark: several methods return constraints. Three possible kinds of constraints a generated:
   unification constraints, convertability constraints and universe level constraints.
   See constraints.h for more details. The first two kinds of constraints are only generated
   if the input expression contains meta-variables or meta-level-parameters.
*/
class type_checker {
    class imp;
    std::unique_ptr<imp> m_ptr;
public:
    type_checker(ro_environment const & env);
    ~type_checker();

    /**
       \brief Return the type of \c e.

       It does not check whether the input expression is type correct or not.
       The contract is: IF the input expression is type correct, then the inferred
       type is correct.
       Throw an exception if a type error is found.

       The result is meaningful only if the resultant set of constraints can be solved.
    */
    std::pair<expr, constraints> infer_type(expr const & e, name_generator & g);

    /**
       \brief Type check the given expression, and return the type of \c e.
       Throw an exception if a type error is found.

       The result is meaningful only if the resultant set of constraints can be solved.
    */
    std::pair<expr, constraints> check(expr const & e, name_generator & g);

    /**
        \brief Return a set of constraints that need to be solved for \c t1 to be convertible to \c t2.

        Return none if \c t1 is not convertible to \c t2.
    */
    optional<constraints> is_convertible(expr const & t1, expr const & t2, name_generator & g);

    /**
        \brief Return a set of constraints that need to be solved for \c t1 to be definitionally equal to \c t2.

        Return none if \c t1 is not definitionally equal to \c t2.
    */
    optional<constraints> is_definitionally_equal(expr const & t1, expr const & t2, name_generator & g);

    /**
        \brief Return a set of constraints that need to be solved for \c e to be a proposition (i.e., it has type Bool)

        Return none if \c e is not a proposition.
    */
    optional<constraints> is_proposition(expr const & e, name_generator & g);

    /**
        \brief Return a Pi if \c e is convertible to a Pi type.
       Throw an exception if a type error is found.
    */
    std::pair<expr, constraints> ensure_pi(expr const & e, name_generator & g);

    /**
        \brief Return a Sigma if \c e is convertible to a Sigma type.
       Throw an exception if a type error is found.
    */
    std::pair<expr, constraints> ensure_sigma(expr const & e, name_generator & g);

    /** \brief Reset internal caches */
    void clear();

    /** \brief Return reference to the normalizer used by this type checker. */
    normalizer & get_normalizer();
};
}
