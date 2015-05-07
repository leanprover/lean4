import algebra.group algebra.category

open eq sigma unit category algebra equiv

set_option pp.implicit true
set_option pp.universes true
set_option pp.notation false
section
  parameters {D₀ : Type} [C : precategory D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type}

  include C
  structure my_structure1 : Type := (vo1 : D₀) (vo2 : D₀)

  check my_structure1

  definition foo2 : Type := my_structure1

  check foo2
end

definition foo3 : Π {D₀ : Type} [C : precategory D₀], Type :=
@my_structure1
