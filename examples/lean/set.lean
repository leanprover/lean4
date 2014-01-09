import macros

definition Set (A : Type) : Type := A → Bool

definition element {A : Type} (x : A) (s : Set A) := s x
infix 60 ∈ : element

definition subset {A : Type} (s1 : Set A) (s2 : Set A) := ∀ x, x ∈ s1 → x ∈ s2
infix 50 ⊆ : subset

theorem subset::trans {A : Type} {s1 s2 s3 : Set A} (H1 : s1 ⊆ s2) (H2 : s2 ⊆ s3) : s1 ⊆ s3
:= λ (x : A) (Hin : x ∈ s1),
      have x ∈ s3 :
        let L1 : x ∈ s2 := H1 x Hin
        in H2 x L1

theorem subset::ext {A : Type} {s1 s2 : Set A} (H : ∀ x, x ∈ s1 = x ∈ s2) : s1 = s2
:= funext H

theorem subset::antisym {A : Type} {s1 s2 : Set A} (H1 : s1 ⊆ s2) (H2 : s2 ⊆ s1) :  s1 = s2
:= subset::ext (have (∀ x, x ∈ s1 = x ∈ s2) :
                   λ x, have x ∈ s1 = x ∈ s2 :
                       boolext (have x ∈ s1 → x ∈ s2 : H1 x)
                               (have x ∈ s2 → x ∈ s1 : H2 x))
