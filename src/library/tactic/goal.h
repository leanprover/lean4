/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <vector>
#include "util/lua.h"
#include "util/list.h"
#include "util/name.h"
#include "kernel/formatter.h"
#include "kernel/expr.h"
#include "kernel/context.h"
#include "kernel/environment.h"

namespace lean {
typedef std::pair<name, expr> hypothesis;
typedef list<hypothesis>      hypotheses;
class goal {
    hypotheses m_hypotheses;
    expr       m_conclusion;
public:
    goal() {}
    goal(hypotheses const & hs, expr const & c);
    hypotheses const & get_hypotheses() const { return m_hypotheses; }
    expr const & get_conclusion() const { return m_conclusion; }
    format pp(formatter const & fmt, options const & opts) const;
    name mk_unique_hypothesis_name(name const & suggestion) const;
};

inline goal update(goal const & g, expr const & c) { return goal(g.get_hypotheses(), c); }
inline goal update(goal const & g, hypotheses const & hs) { return goal(hs, g.get_conclusion()); }
inline goal update(goal const & g, buffer<hypothesis> const & hs) { return goal(to_list(hs.begin(), hs.end()), g.get_conclusion()); }
inline hypotheses add_hypothesis(name const & h_name, expr const & h, hypotheses const & hs) {
    return cons(mk_pair(h_name, h), hs);
}
inline hypotheses add_hypothesis(hypothesis const & h, hypotheses const & hs) {
    return cons(h, hs);
}

/**
   \brief Functor for converting a proof for a goal \c g produced using <tt>to_goal(env, ctx, T)</tt>
   into a term of type \c t.

   That is, the goal was created to synthesize a proof term for a proposition/type \c T in a
   context \c ctx. This functor allows us to convert a proof for \c g into a term/expression \c p
   s.t. <tt>ctx |- p : T</t>
*/
class goal_proof_fn {
    friend std::pair<goal, goal_proof_fn> to_goal(ro_environment const & env, context const & ctx, expr const & t);
    std::vector<expr> m_constants;
    goal_proof_fn(std::vector<expr> && constants);
public:
    expr operator()(expr const & pr) const;
};

/**
   \brief Convert the synthesis problem <tt>ctx |- ?p : T</tt> into a goal,
   where \c T is a proposition (i.e., has type Boolean), and \c ?p is a proof we want to synthesize.

   We can use tactics for solving the resultant goal, and the functor \c goal_proof_fn
   to convert the proof for the goal into the proof term \c ?p.
*/
std::pair<goal, goal_proof_fn> to_goal(ro_environment const & env, context const & ctx, expr const & t);

UDATA_DEFS_CORE(hypotheses)
UDATA_DEFS(goal)
void open_goal(lua_State * L);
}
