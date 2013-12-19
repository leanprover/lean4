Definition Set (A : Type) : Type := A → Bool

Definition element {A : Type} (x : A) (s : Set A) := s x
Infix 60 ∈ : element

Definition subset {A : Type} (s1 : Set A) (s2 : Set A) := ∀ x, x ∈ s1 ⇒ x ∈ s2
Infix 50 ⊆ : subset

Theorem SubsetProp {A : Type} {s1 s2 : Set A} {x : A} (H1 : s1 ⊆ s2) (H2 : x ∈ s1) : x ∈ s2 :=
   MP (ForallElim H1 x) H2

Theorem SubsetTrans {A : Type} {s1 s2 s3 : Set A} (H1 : s1 ⊆ s2) (H2 : s2 ⊆ s3) : s1 ⊆ s3 :=
   ForallIntro (λ x,
       Discharge (λ Hin : x ∈ s1,
          let L1 : x ∈ s2 := SubsetProp H1 Hin,
              L2 : x ∈ s3 := SubsetProp H2 L1
          in  L2)).

Definition transitive {A : Type} (R : A → A → Bool) := ∀ x y z, R x y ⇒ R y z ⇒ R x z

Theorem SubsetTrans2 {A : Type} : transitive (subset::explicit A) :=
   ForallIntro (λ s1, ForallIntro (λ s2, ForallIntro (λ s3,
      Discharge (λ H1, (Discharge (λ H2,
         SubsetTrans H1 H2)))))).

Theorem SubsetRefl {A : Type} (s : Set A) : s ⊆ s :=
   ForallIntro (λ x, Discharge (λ H : x ∈ s, H))

Definition union {A : Type} (s1 : Set A) (s2 : Set A) := λ x, x ∈ s1 ∨ x ∈ s2
Infix 55 ∪ : union
