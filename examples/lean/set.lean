Import macros

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

Theorem SubsetExt (A : Type) : ∀ s1 s2 : Set A, (∀ x, x ∈ s1 = x ∈ s2) ⇒ s1 = s2 :=
   for s1 s2, assume (H : ∀ x, x ∈ s1 = x ∈ s2),
       Abst (fun x, instantiate H x)

Theorem SubsetAntiSymm (A : Type) : ∀ s1 s2 : Set A, s1 ⊆ s2 ⇒ s2 ⊆ s1 ⇒ s1 = s2 :=
   for s1 s2, assume (H1 : s1 ⊆ s2) (H2 : s2 ⊆ s1),
       show s1 = s2,
            MP (show (∀ x, x ∈ s1 = x ∈ s2) ⇒ s1 = s2,
                     instantiate (SubsetExt A) s1 s2)
               (show (∀ x, x ∈ s1 = x ∈ s2),
                     for x, show x ∈ s1 = x ∈ s2,
                                 let L1 : x ∈ s1 ⇒ x ∈ s2 := instantiate H1 x,
                                     L2 : x ∈ s2 ⇒ x ∈ s1 := instantiate H2 x
                                     in ImpAntisym L1 L2)

(* Compact (but less readable) version of the previous theorem *)
Theorem SubsetAntiSymm2 (A : Type) : ∀ s1 s2 : Set A, s1 ⊆ s2 ⇒ s2 ⊆ s1 ⇒ s1 = s2 :=
   for s1 s2, assume H1 H2,
      MP (instantiate (SubsetExt A) s1 s2)
         (for x, ImpAntisym (instantiate H1 x) (instantiate H2 x))
