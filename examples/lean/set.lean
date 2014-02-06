import macros

definition Set (A : Type) : Type := A → Bool

definition element {A : Type} (x : A) (s : Set A) := s x
infix 60 ∈ : element

definition subset {A : Type} (s1 : Set A) (s2 : Set A) := ∀ x, x ∈ s1 → x ∈ s2
infix 50 ⊆ : subset

theorem subset_trans {A : Type} {s1 s2 s3 : Set A} (H1 : s1 ⊆ s2) (H2 : s2 ⊆ s3) : s1 ⊆ s3
:= take x : A,
      assume Hin : x ∈ s1,
          show x ∈ s3, from
             let L1 : x ∈ s2 := H1 x Hin
             in H2 x L1

theorem subset_ext {A : Type} {s1 s2 : Set A} (H : ∀ x, x ∈ s1 = x ∈ s2) : s1 = s2
:= funext H

theorem subset_antisym {A : Type} {s1 s2 : Set A} (H1 : s1 ⊆ s2) (H2 : s2 ⊆ s1) :  s1 = s2
:= subset_ext (show (∀ x, x ∈ s1 = x ∈ s2), from
                   take x, show x ∈ s1 = x ∈ s2, from
                       boolext (show x ∈ s1 → x ∈ s2, from H1 x)
                               (show x ∈ s2 → x ∈ s1, from H2 x))
