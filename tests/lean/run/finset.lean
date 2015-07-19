import data.list
open list setoid quot decidable nat

namespace finset

  definition eqv {A : Type} (l₁ l₂ : list A) :=
  ∀ a, a ∈ l₁ ↔ a ∈ l₂

  infix `~` := eqv

  theorem eqv.refl {A : Type} (l : list A) : l ~ l :=
  λ a, !iff.refl

  theorem eqv.symm {A : Type} {l₁ l₂ : list A} : l₁ ~ l₂ → l₂ ~ l₁ :=
  λ H a, iff.symm (H a)

  theorem eqv.trans {A : Type} {l₁ l₂ l₃ : list A} : l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃ :=
  λ H₁ H₂ a, iff.trans (H₁ a) (H₂ a)

  theorem eqv.is_equivalence (A : Type) : equivalence (@eqv A) :=
  and.intro (@eqv.refl A) (and.intro (@eqv.symm A) (@eqv.trans A))

  definition norep {A : Type} [H : decidable_eq A] : list A → list A
  | []        :=  []
  | (x :: xs) :=  if x ∈ xs then norep xs else x :: norep xs

  definition eqv_norep {A : Type} [H : decidable_eq A] : ∀ l : list A, l ~ norep l
  | []        := (λ a, iff.rfl)
  | (x :: xs) :=
    take y,
    assert ih : xs ~ norep xs, from eqv_norep xs,
    show y ∈ x :: xs ↔ y ∈ if x ∈ xs then norep xs else x :: norep xs,
    begin
      apply (@by_cases (x ∈ xs)),
      begin
        intro xin, rewrite (if_pos xin),
        apply iff.intro,
        {intro yinxxs, apply (or.elim (iff.mp !mem_cons_iff yinxxs)),
          intro yeqx,  rewrite -yeqx at xin, exact (iff.mp (ih y) xin),
          intro yeqxs, exact (iff.mp (ih y) yeqxs)},
        {intro yinnrep, show y ∈ x::xs, from or.inr (iff.mpr (ih y) yinnrep)}
      end,
      begin
        intro xnin, rewrite (if_neg xnin),
        apply iff.intro,
        {intro yinxxs, apply (or.elim (iff.mp !mem_cons_iff yinxxs)),
          intro yeqx, rewrite yeqx, apply mem_cons,
          intro yinxs, show y ∈ x:: norep xs, from or.inr (iff.mp (ih y) yinxs)},
        {intro yinxnrep, apply (or.elim (iff.mp !mem_cons_iff yinxnrep)),
          intro yeqx, rewrite yeqx, apply mem_cons,
          intro yinrep, show y ∈ x::xs, from or.inr (iff.mpr (ih y) yinrep)}
      end
    end

  definition sub {A : Type} (l₁ l₂ : list A) := ∀ a, a ∈ l₁ → a ∈ l₂

  infix ⊆ := sub

  theorem eqv_of_sub_of_sub {A : Type} {l₁ l₂ : list A} : l₁ ⊆ l₂ → l₂ ⊆ l₁ → l₁ ~ l₂ :=
  assume h₁ h₂ a, iff.intro (h₁ a) (h₂ a)

  theorem sub_of_eqv_left {A : Type} {l₁ l₂ : list A} : l₁ ~ l₂ → l₁ ⊆ l₂ :=
  assume h₁ a ainl₁, iff.mp (h₁ a) ainl₁

  theorem sub_of_eqv_right {A : Type} {l₁ l₂ : list A} : l₁ ~ l₂ → l₂ ⊆ l₁ :=
  assume h₁ a ainl₂, iff.mpr (h₁ a) ainl₂

  definition sub_of_cons_sub {A : Type} {a : A} {l₁ l₂ : list A} : a :: l₁ ⊆ l₂ → l₁ ⊆ l₂ :=
  assume s, take b, assume binl₁, s b (or.inr binl₁)

  definition decidable_sub [instance] {A : Type} [H : decidable_eq A] : ∀ l₁ l₂ : list A, decidable (l₁ ⊆ l₂)
  | []      ys      := inl (λ a h, absurd h !not_mem_nil)
  | (x::xs) ys      :=
    if xinys : x ∈ ys then
      match decidable_sub xs ys with
      | (inl xs_sub_ys)  := inl (λ y yinxxs, or.elim (iff.mp !mem_cons_iff yinxxs)
         (λ yeqx, by rewrite yeqx; exact xinys)
         (λ yinxs, xs_sub_ys y yinxs))
      | (inr nxs_sub_ys) := inr (λ h, absurd (sub_of_cons_sub h) nxs_sub_ys)
      end
    else
      inr (λ h, absurd (h x !mem_cons) xinys)

  example : [(1 : nat), 2, 3] ⊆ [1,3,4,1,2] :=
  dec_trivial

  definition decidable_eqv [instance] {A : Type} [H : decidable_eq A] : ∀ l₁ l₂ : list A, decidable (l₁ ~ l₂) :=
  take l₁ l₂ : list A,
  match decidable_sub l₁ l₂ with
  | (inl s₁) :=
    match decidable_sub l₂ l₁ with
    | (inl s₂) := inl (eqv_of_sub_of_sub s₁ s₂)
    | (inr n₂) := inr (λ h, absurd (sub_of_eqv_right h) n₂)
    end
  | (inr n₁) := inr (λ h, absurd (sub_of_eqv_left h) n₁)
  end

  example : [(1:nat), 2, 3, 2, 2, 2] ~ [1,3,3,1,2] :=
  dec_trivial

  definition finset_setoid [instance] (A : Type) : setoid (list A) :=
  setoid.mk (@eqv A) (eqv.is_equivalence A)

  definition finset (A : Type) : Type :=
  quot (finset_setoid A)

  definition has_decidable_eq [instance] {A : Type} [H : decidable_eq A] : ∀ s₁ s₂ : finset A, decidable (s₁ = s₂) :=
  take s₁ s₂, quot.rec_on_subsingleton₂ s₁ s₂
   (take l₁ l₂,
      match decidable_eqv l₁ l₂ with
      | inl e := inl (quot.sound e)
      | inr d := inr (λ e, absurd (quot.exact e) d)
      end)

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
          intro inl₃, exact (mem_append_of_mem_or_mem (or.inl (iff.mpr (r₁ a) inl₃))),
          intro inl₄, exact (mem_append_of_mem_or_mem (or.inr (iff.mpr (r₂ a) inl₄)))
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

  example : to_finset [(1:nat), 1, 2, 3] = to_finset [2, 3, 1, 2, 2, 3] :=
  dec_trivial

  example : to_finset [(1:nat), 1, 4, 2, 3] ≠ to_finset [2, 3, 1, 2, 2, 3] :=
  dec_trivial

  definition clean {A : Type} [H : decidable_eq A] (s : finset A) : finset A :=
  quot.lift_on s (λ l, ⟦norep l⟧)
   (λ l₁ l₂ e, calc
     ⟦norep l₁⟧  = ⟦l₁⟧       : quot.sound (eqv_norep l₁)
            ...  = ⟦l₂⟧       : quot.sound e
            ...  = ⟦norep l₂⟧ : quot.sound (eqv_norep l₂))

  theorem eq_clean {A : Type} [H : decidable_eq A] : ∀ s : finset A, clean s = s :=
  take s, quot.induction_on s (λ l, eq.symm (quot.sound (eqv_norep l)))

  theorem eq_of_clean_eq_clean {A : Type} [H : decidable_eq A] : ∀ s₁ s₂ : finset A, clean s₁ = clean s₂ → s₁ = s₂ :=
  take s₁ s₂, by rewrite *eq_clean; intro H; apply H

  example : to_finset [(1:nat), 1, 2, 3] = to_finset [1, 2, 2, 2, 3, 3] :=
  !eq_of_clean_eq_clean rfl
end finset
