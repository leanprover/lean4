open list nat

namespace toy
constants (A : Type.{1}) (f h : A → A) (x y z : A)
attribute [irreducible]
noncomputable definition g (x y : A) : A := f z

@[unify]
noncomputable definition toy_hint (x y : A) : unification_hint :=
{ pattern     := g x y ≟ f z,
  constraints := [] }

open tactic

set_option trace.type_context.unification_hint true

definition ex1 (a : A) (H : g x y = a) : f z = a :=
by do {trace_state, assumption}

#print ex1
end toy

namespace add
constants (n : ℕ)
attribute  [irreducible] add

open tactic

@[unify]
definition add_zero_hint (m n : ℕ) [has_add ℕ] [has_one ℕ] [has_zero ℕ] : unification_hint :=
{ pattern     := m + 1 ≟ succ n,
  constraints := [m ≟ n] }

definition ex2 (H : n + 1 = 0) : succ n = 0 :=
by assumption

#print ex2

end add
