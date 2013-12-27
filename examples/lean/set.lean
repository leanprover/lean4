(**
-- import macros for, assume, mp, ...
import("macros.lua")
**)

Definition Set (A : Type) : Type := A → Bool

Definition element {A : Type} (x : A) (s : Set A) := s x
Infix 60 ∈ : element

Definition subset {A : Type} (s1 : Set A) (s2 : Set A) := ∀ x, x ∈ s1 ⇒ x ∈ s2
Infix 50 ⊆ : subset

Theorem SubsetTrans (A : Type) : ∀ s1 s2 s3 : Set A, s1 ⊆ s2 ⇒ s2 ⊆ s3 ⇒ s1 ⊆ s3 :=
   for s1 s2 s3, assume (H1 : s1 ⊆ s2) (H2 : s2 ⊆ s3),
      show s1 ⊆ s3,
        for x, assume Hin : x ∈ s1,
           show x ∈ s3,
             let L1 : x ∈ s2 := mp (instantiate H1 x) Hin
             in mp (instantiate H2 x) L1
