/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "util/buffer.h"
#include "kernel/expr.h"
#include "kernel/context.h"
#include "kernel/unification_constraint.h"

namespace lean {
class environment;
class metavar_env;
/**
   \brief Functional object for "quickly" inferring the type of expressions.
   It does not check whether the input expression is type correct or not.
   The contract is: IF the input expression is type correct, then the inferred
   type is correct.

   \remark The exceptions produced by this class are not informative.
   That is, they are not meant for external users, but to sign that the
   type could not be inferred.
*/
class light_checker {
    class imp;
    std::unique_ptr<imp> m_ptr;
public:
    light_checker(environment const & env);
    ~light_checker();

    expr operator()(expr const & e, context const & ctx, metavar_env * menv, buffer<unification_constraint> & uc);
    expr operator()(expr const & e, context const & ctx = context());

    void clear();

    void set_interrupt(bool flag);
    void interrupt() { set_interrupt(true); }
    void reset_interrupt() { set_interrupt(false); }
};
}
