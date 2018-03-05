/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"
#include "library/expr_pair.h"
#include "library/io_state.h"
#include "library/head_map.h"
#include "util/priority_queue.h"

namespace lean {

/*
Users can declare unification hints using the following structures:

structure unification_constraint := {A : Type} (lhs : A) (rhs : A)
structure unification_hint := (pattern : unification_constraint) (constraints : list unification_constraint)

Example:

definition both_zero_of_add_eq_zero [unify] (n₁ n₂ : ℕ) (s₁ : has_add ℕ) (s₂ : has_zero ℕ) : unification_hint :=
  unification_hint.mk (unification_constraint.mk (@has_add.add ℕ s₁ n₁ n₂) (@has_zero.zero ℕ s₂))
    [unification_constraint.mk n₁ (@has_zero.zero ℕ s₂),
     unification_constraint.mk n₂ (@has_zero.zero ℕ s₂)]

creates the following unification hint:
m_lhs: add nat #1 #3 #2
m_rhs: zero nat #0
m_constraints: [(#3, zero nat #0), (#2, zero nat #0)]
m_num_vars: #4

Note that once we have an assignment to all variables from matching, we must substitute the assignments in the constraints.
*/
class unification_hint {
    expr m_lhs;
    expr m_rhs;

    list<expr_pair> m_constraints;
    unsigned m_num_vars;
public:
    expr get_lhs() const { return m_lhs; }
    expr get_rhs() const { return m_rhs; }
    list<expr_pair> get_constraints() const { return m_constraints; }
    unsigned get_num_vars() const { return m_num_vars; }

    unification_hint() {}
    unification_hint(expr const & lhs, expr const & rhs, list<expr_pair> const & constraints, unsigned num_vars);
    format pp(unsigned priority, formatter const & fmt) const;
};

struct unification_hint_cmp {
    int operator()(unification_hint const & uh1, unification_hint const & uh2) const;
};

typedef priority_queue<unification_hint, unification_hint_cmp> unification_hint_queue;
typedef rb_map<name_pair, unification_hint_queue, name_pair_quick_cmp> unification_hints;

unification_hints get_unification_hints(environment const & env);
void get_unification_hints(unification_hints const & hints, name const & n1, name const & n2, buffer<unification_hint> & uhints);

void get_unification_hints(environment const & env, name const & n1, name const & n2, buffer<unification_hint> & hints);

format pp_unification_hints(unification_hints const & hints, formatter const & fmt);

class type_context_old;
bool try_unification_hint(type_context_old & o, unification_hint const & hint, expr const & lhs, expr const & rhs);

void initialize_unification_hint();
void finalize_unification_hint();
}
