open list nat

structure unification_constraint := {A : Type} (lhs : A) (rhs : A)
structure unification_hint := (pattern : unification_constraint) (constraints : list unification_constraint)

namespace toy
constants (A : Type.{1}) (f h : A → A) (x y z : A)
definition g [irreducible] (x y : A) : A := f z

definition toy_hint [unify] (x y : A) : unification_hint :=
  unification_hint.mk (unification_constraint.mk (g x y) (f z)) []

open tactic

set_option trace.type_context.unification_hint true

definition ex1 (a : A) (H : g x y = a) : f z = a :=
by do {trace_state, assumption}

print ex1
end toy

namespace add
constants (n : ℕ)
attribute add [irreducible]

open tactic

definition add_zero_hint [unify] (m n : ℕ) [has_add ℕ] [has_one ℕ] [has_zero ℕ] : unification_hint :=
  unification_hint.mk (unification_constraint.mk (m + 1) (succ n)) [unification_constraint.mk m n]

definition ex2 (H : n + 1 = 0) : succ n = 0 :=
by assumption

print ex2

end add
