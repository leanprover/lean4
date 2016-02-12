import data.list data.nat
open list nat

structure unification_constraint := {A : Type} (lhs : A) (rhs : A)
structure unification_hint := (pattern : unification_constraint) (constraints : list unification_constraint)

namespace toy
constants (A : Type.{1}) (f h : A → A) (x y z : A)
definition g [irreducible] (x y : A) : A := f z

#unify (g x y), (f z)

definition toy_hint [unify] (x y : A) : unification_hint :=
  unification_hint.mk (unification_constraint.mk (g x y) (f z)) []

#unify (g x y), (f z)
print [unify]

end toy

namespace add
constants (n : ℕ)

#unify (n + 1), succ n

definition add_zero_hint [unify] (m n : ℕ) [has_add ℕ] [has_one ℕ] [has_zero ℕ] : unification_hint :=
  unification_hint.mk (unification_constraint.mk (m + 1) (succ n)) [unification_constraint.mk m n]

#unify (n + 1), (succ n)
print [unify]

end add

namespace canonical
structure Canonical := (carrier : Type) (op : carrier → carrier)
attribute Canonical.carrier [irreducible]

constants (A : Type.{1}) (f : A → A) (x : A)
definition A_canonical : Canonical := Canonical.mk A f

#unify (Canonical.carrier A_canonical), A

definition Canonical_hint [unify] (C : Canonical) : unification_hint :=
  unification_hint.mk (unification_constraint.mk (Canonical.carrier C) A) [unification_constraint.mk C A_canonical]

-- TODO(dhs): we mark carrier as irreducible and prove A_canonical explicitly to work around the fact that
-- the default_type_context does not recognize the elaborator metavariables as metavariables,
-- and so cannot perform the assignment.
#unify (Canonical.carrier A_canonical), A
print [unify]

end canonical

print [unify] canonical
