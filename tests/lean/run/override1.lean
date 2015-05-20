import data.finset data.set

open set

example (A : Type) (x : A) (S H : set A) (Pin : x ∈ S)
  (Psub : S ⊆ H) : x ∈ H := Psub Pin

open finset

section
  override set -- set notation overrides existing one

  example (A : Type) (x : A) (S H : set A) (Pin : x ∈ S)
    (Psub : S ⊆ H) : x ∈ H := Psub Pin
end

-- ⊆ is now overloaded
example (A : Type) (x : A) (S H : set A) (Pin : x ∈ S)
  (Psub : S ⊆ H) : x ∈ H := Psub _ Pin


override set -- overrides existing notation

example (A : Type) (x : A) (S H : set A) (Pin : x ∈ S) (Psub : S ⊆ H) : x ∈ H := Psub Pin
