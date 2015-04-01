import logic.axioms.extensional data.list
open list setoid quot

namespace finset

  definition eqv {A : Type} (l₁ l₂ : list A) :=
  ∀ a, a ∈ l₁ ↔ a ∈ l₂

  infix `∼` := eqv

  theorem eqv.refl {A : Type} (l : list A) : l ∼ l :=
  λ a, !iff.refl

  theorem eqv.symm {A : Type} {l₁ l₂ : list A} : l₁ ∼ l₂ → l₂ ∼ l₁ :=
  λ H a, iff.symm (H a)

  theorem eqv.trans {A : Type} {l₁ l₂ l₃ : list A} : l₁ ∼ l₂ → l₂ ∼ l₃ → l₁ ∼ l₃ :=
  λ H₁ H₂ a, iff.trans (H₁ a) (H₂ a)

  theorem eqv.is_equivalence (A : Type) : equivalence (@eqv A) :=
  and.intro (@eqv.refl A) (and.intro (@eqv.symm A) (@eqv.trans A))

  definition finset_setoid [instance] (A : Type) : setoid (list A) :=
  setoid.mk (@eqv A) (eqv.is_equivalence A)

  definition finset (A : Type) : Type :=
  quot (finset_setoid A)

  definition to_finset {A : Type} (l : list A) : finset A :=
  ⟦l⟧

  definition mem {A : Type} (a : A) (s : finset A) : Prop :=
  quot.lift_on s
    (λ l : list A, a ∈ l)
    (λ l₁ l₂ r, propext (r a))

  infix ∈ := mem

  theorem mem_list {A : Type} {a : A} {l : list A} : a ∈ l → a ∈ ⟦l⟧ :=
  λ H, H

  definition empty {A : Type} : finset A :=
  ⟦nil⟧

  notation `∅` := empty

  definition union {A : Type} (s₁ s₂ : finset A) : finset A :=
  quot.lift_on₂ s₁ s₂
    (λ l₁ l₂ : list A, ⟦l₁ ++ l₂⟧)
    (λ l₁ l₂ l₃ l₄ r₁ r₂,
      begin
        apply quot.sound,
        intro a,
        apply iff.intro,
        begin
          intro inl₁l₂,
          apply (or.elim (mem_or_mem_of_mem_append inl₁l₂)),
          intro inl₁, exact (mem_append_of_mem_or_mem (or.inl (iff.mp (r₁ a) inl₁))),
          intro inl₂, exact (mem_append_of_mem_or_mem (or.inr (iff.mp (r₂ a) inl₂)))
        end,
        begin
          intro inl₃l₄,
          apply (or.elim (mem_or_mem_of_mem_append inl₃l₄)),
          intro inl₃, exact (mem_append_of_mem_or_mem (or.inl (iff.mp' (r₁ a) inl₃))),
          intro inl₄, exact (mem_append_of_mem_or_mem (or.inr (iff.mp' (r₂ a) inl₄)))
        end,
      end)

  infix `∪` := union

  theorem mem_union_left {A : Type} (s₁ s₂ : finset A) (a : A) : a ∈ s₁ → a ∈ s₁ ∪ s₂ :=
  quot.ind₂ (λ l₁ l₂ ainl₁, mem_append_left l₂ ainl₁) s₁ s₂

  theorem mem_union_right {A : Type} (s₁ s₂ : finset A) (a : A) : a ∈ s₂ → a ∈ s₁ ∪ s₂ :=
  quot.ind₂ (λ l₁ l₂ ainl₂, mem_append_right l₁ ainl₂) s₁ s₂

  theorem union_empty {A : Type} (s : finset A) : s ∪ ∅ = s :=
  quot.induction_on s (λ l, quot.sound (λ a, by rewrite append_nil_right))

  theorem empty_union {A : Type} (s : finset A) : ∅ ∪ s = s :=
  quot.induction_on s (λ l, quot.sound (λ a, by rewrite append_nil_left))

  example : to_finset (1::2::nil) ∪ to_finset (2::3::nil) = ⟦1 :: 2 :: 2 :: 3 :: nil⟧ :=
  rfl

end finset
