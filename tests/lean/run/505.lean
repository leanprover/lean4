import data.set
open set

section
  variable {A : Type}

  definition set_of (P : A → Prop) : set A := P

  notation `{` binders `|` r:(scoped:1 P, set_of P) `}` := r

  definition insert (a : A) (s : set A) : set A := {x : A | x = a ∨ x ∈ s}

  notation `⦃` s:(foldr `,` (a t, insert a t) ∅) `⦄` := s
  notation `{` `{` s:(foldr `,` (a t, insert a t) ∅) `}` `}` := s

  check ⦃1, 2, 3⦄
  check {{1, 2, 3}}

  definition foo  {X : Type} {{ x : X }} : X := x
end
