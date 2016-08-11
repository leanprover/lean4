/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "library/metavar.h"
#include "library/equations_compiler/old_goal.h"


namespace lean {
namespace inversion {
/**
   \brief When we apply the inversion tactic/procedure on a hypothesis (h : I A j), where
   I is an inductive datatpe, the hypothesis is "broken" into cases: one for each constructor.
   Some cases may be in conflict with the type (I A j) and may be suppressed.

   Example of conflict: given the vector type
      inductive vector (A : Type) : nat → Type :=
      nil {} : vector A zero,
      cons   : Π {n : nat}, A → vector A n → vector A (succ n)
   Then, (h : vector A (succ n)) is in conflict with constructor nil.

   The user may provide possible implementations (example: in the form of equations).
   Each possible implementation is associated with a case/constructor.

   The inversion tactic/procedure distributes the implementations over cases.

   The implementations may depend on hypotheses that may be modifed by the inversion procedure.
   The method update_exprs of each implementation is invoked to update the expressions of
   a given implementation.
*/
class implementation {
public:
    virtual ~implementation() {}
    virtual name const & get_constructor_name() const = 0;
    virtual void update_exprs(std::function<expr(expr const &)> const & fn) = 0;
};

typedef std::shared_ptr<implementation> implementation_ptr;
typedef list<implementation_ptr> implementation_list;

struct result {
    list<old_goal>             m_goals;
    list<list<expr>>           m_args; // arguments of the constructor/intro rule
    list<implementation_list>  m_implementation_lists;
    list<rename_map>           m_renames;
    // invariant: length(m_goals) == length(m_args);
    // invariant: length(m_goals) == length(m_implementation_lists);
    // invariant: length(m_goals) == length(m_renames);
    substitution               m_subst;
    result(list<old_goal> const & gs, list<list<expr>> const & args, list<implementation_list> const & imps,
           list<rename_map> const & rs, substitution const & subst);
};

optional<result> apply(environment const & env, io_state const & ios, old_type_checker & tc,
                       old_goal const & g, expr const & h, implementation_list const & imps,
                       bool clear_elim);
}
}
