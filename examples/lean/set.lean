import macros

definition Set (A : Type) : Type := A → Bool

definition element {A : Type} (x : A) (s : Set A) := s x
infix 60 ∈ : element

definition subset {A : Type} (s1 : Set A) (s2 : Set A) := ∀ x, x ∈ s1 ⇒ x ∈ s2
infix 50 ⊆ : subset

theorem subset::trans (A : Type) : ∀ s1 s2 s3 : Set A, s1 ⊆ s2 ⇒ s2 ⊆ s3 ⇒ s1 ⊆ s3 :=
   take s1 s2 s3, assume (H1 : s1 ⊆ s2) (H2 : s2 ⊆ s3),
      have s1 ⊆ s3 :
        take x, assume Hin : x ∈ s1,
           have x ∈ s3 :
             let L1 : x ∈ s2 := H1 ↓ x ◂ Hin
             in H2 ↓ x ◂ L1

theorem subset::ext (A : Type) : ∀ s1 s2 : Set A, (∀ x, x ∈ s1 = x ∈ s2) ⇒ s1 = s2 :=
   take s1 s2, assume (H : ∀ x, x ∈ s1 = x ∈ s2),
       abst (λ x, H ↓ x)

theorem subset::antisym (A : Type) : ∀ s1 s2 : Set A, s1 ⊆ s2 ⇒ s2 ⊆ s1 ⇒ s1 = s2 :=
   take s1 s2, assume (H1 : s1 ⊆ s2) (H2 : s2 ⊆ s1),
       have s1 = s2 :
            (have (∀ x, x ∈ s1 = x ∈ s2) ⇒ s1 = s2 :
                  (subset::ext A) ↓ s1 ↓ s2)
            ◂ (have (∀ x, x ∈ s1 = x ∈ s2) :
                    take x, have x ∈ s1 = x ∈ s2 :
                       iff::intro (have x ∈ s1 ⇒ x ∈ s2 : H1 ↓ x)
                                  (have x ∈ s2 ⇒ x ∈ s1 : H2 ↓ x))


-- Compact (but less readable) version of the previous theorem
theorem subset::antisym2 (A : Type) : ∀ s1 s2 : Set A, s1 ⊆ s2 ⇒ s2 ⊆ s1 ⇒ s1 = s2 :=
   take s1 s2, assume H1 H2,
     (subset::ext A) ↓ s1 ↓ s2 ◂ (take x, iff::intro (H1 ↓ x) (H2 ↓ x))
