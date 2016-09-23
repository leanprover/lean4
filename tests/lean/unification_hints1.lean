--
open list nat

structure unification_constraint := {A : Type*} (lhs : A) (rhs : A)
structure unification_hint := (pattern : unification_constraint) (constraints : list unification_constraint)

namespace toy
constants (A : Type) (f h : A → A) (x y z : A)
attribute [irreducible]
noncomputable definition g (x y : A) : A := f z

#unify (g x y), (f z)

attribute [unify]
noncomputable definition toy_hint (x y : A) : unification_hint :=
{ pattern := {lhs := g x y, rhs := f z}, constraints := [] }

infix `=?=`:50 := unification_constraint.mk

#unify (g x y), (f z)
print [unify]

end toy

namespace add
constants (n : ℕ)
attribute add [irreducible]

#unify (n + 1), succ n

attribute [unify]
definition add_zero_hint (m n : ℕ) [has_add ℕ] [has_one ℕ] [has_zero ℕ] : unification_hint :=
{ pattern := m + 1 =?= succ n, constraints := [m =?= n] }

#unify (n + 1), (succ n)
print [unify]

end add

namespace canonical
inductive Canonical
| mk : Π (carrier : Type*) (op : carrier → carrier), Canonical

attribute [irreducible]
definition Canonical.carrier (s : Canonical) : Type* :=
Canonical.rec_on s (λ c op, c)

constants (A : Type) (f : A → A) (x : A)
noncomputable definition A_canonical : Canonical := Canonical.mk A f

#unify (Canonical.carrier A_canonical), A

attribute [unify]
noncomputable definition Canonical_hint (C : Canonical) : unification_hint :=
{ pattern := C~>carrier =?= A, constraints := [C =?= A_canonical] }

-- TODO(dhs): we mark carrier as irreducible and prove A_canonical explicitly to work around the fact that
-- the default_type_context does not recognize the elaborator metavariables as metavariables,
-- and so cannot perform the assignment.
#unify (Canonical.carrier A_canonical), A
print [unify]

end canonical
