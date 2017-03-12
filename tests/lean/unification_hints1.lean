--
open list nat

namespace toy
constants (A : Type) (f h : A → A) (x y z : A)
attribute [irreducible]
noncomputable definition g (x y : A) : A := f z

#unify (g x y), (f z)

@[unify]
noncomputable definition toy_hint (x y : A) : unification_hint :=
{ pattern := g x y ≟ f z,
  constraints := [] }

#unify (g x y), (f z)
#print [unify]

end toy


namespace canonical
inductive Canonical
| mk : Π (carrier : Type*) (op : carrier → carrier), Canonical

attribute [irreducible]
definition Canonical.carrier (s : Canonical) : Type* :=
Canonical.rec_on s (λ c op, c)

constants (A : Type) (f : A → A) (x : A)
noncomputable definition A_canonical : Canonical := Canonical.mk A f

#unify (Canonical.carrier A_canonical), A

@[unify]
noncomputable definition Canonical_hint (C : Canonical) : unification_hint :=
{ pattern     := C~>carrier ≟ A,
  constraints := [C ≟ A_canonical] }

-- TODO(dhs): we mark carrier as irreducible and prove A_canonical explicitly to work around the fact that
-- the default_type_context does not recognize the elaborator metavariables as metavariables,
-- and so cannot perform the assignment.
#unify (Canonical.carrier A_canonical), A
#print [unify]

end canonical
