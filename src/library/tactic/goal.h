/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <vector>
#include "util/list.h"
#include "util/name.h"
#include "kernel/expr.h"
#include "kernel/context.h"
#include "kernel/environment.h"

namespace lean {
class goal {
    list<std::pair<name, expr>> m_hypotheses;
    expr                        m_conclusion;
public:
    goal(list<std::pair<name, expr>> const & h, expr const & c);
    list<std::pair<name, expr>> const & get_hypotheses() const { return m_hypotheses; }
    expr const & get_conclusion() const { return m_conclusion; }
};

/**
   \brief Functor for converting a proof for a goal \c g produced using <tt>to_goal(env, ctx, T)</tt>
   into a term of type \c t.

   That is, the goal was created to synthesize a proof term for a proposition/type \c T in a
   context \c ctx. This functor allows us to convert a proof for \c g into a term/expression \c p
   s.t. <tt>ctx |- p : T</t>
*/
class goal_proof_fn {
    friend std::pair<goal, goal_proof_fn> to_goal(environment const & env, context const & ctx, expr const & t);
    std::vector<expr> m_constants;
    goal_proof_fn(std::vector<expr> && constants);
public:
    expr operator()(expr const & pr);
};

/**
   \brief Convert the synthesis problem <tt>ctx |- ?p : T</tt> into a goal,
   where \c T is a proposition (i.e., has type Boolean), and \c ?p is a proof we want to synthesize.

   We can use tactics for solving the resultant goal, and the functor \c goal_proof_fn
   to convert the proof for the goal into the proof term \c ?p.
*/
std::pair<goal, goal_proof_fn> to_goal(environment const & env, context const & ctx, expr const & t);
}
