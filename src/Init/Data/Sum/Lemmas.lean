/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
prelude
import Init.Data.Sum.Basic
import Init.Ext

/-!
# Disjoint union of types

Theorems about the definitions introduced in `Init.Data.Sum.Basic`.
-/

open Function

namespace Sum

@[simp] protected theorem «forall» {p : α ⊕ β → Prop} :
    (∀ x, p x) ↔ (∀ a, p (inl a)) ∧ ∀ b, p (inr b) :=
  ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩, fun ⟨h₁, h₂⟩ => Sum.rec h₁ h₂⟩

@[simp] protected theorem «exists» {p : α ⊕ β → Prop} :
    (∃ x, p x) ↔ (∃ a, p (inl a)) ∨ ∃ b, p (inr b) :=
  ⟨ fun
    | ⟨inl a, h⟩ => Or.inl ⟨a, h⟩
    | ⟨inr b, h⟩ => Or.inr ⟨b, h⟩,
    fun
    | Or.inl ⟨a, h⟩ => ⟨inl a, h⟩
    | Or.inr ⟨b, h⟩ => ⟨inr b, h⟩⟩

theorem forall_sum {γ : α ⊕ β → Sort _} (p : (∀ ab, γ ab) → Prop) :
    (∀ fab, p fab) ↔ (∀ fa fb, p (Sum.rec fa fb)) := by
  refine ⟨fun h fa fb => h _, fun h fab => ?_⟩
  have h1 : fab = Sum.rec (fun a => fab (Sum.inl a)) (fun b => fab (Sum.inr b)) := by
    apply funext
    rintro (_ | _) <;> rfl
  rw [h1]; exact h _ _

section get

@[simp] theorem inl_getLeft : ∀ (x : α ⊕ β) (h : x.isLeft), inl (x.getLeft h) = x
  | inl _, _ => rfl
@[simp] theorem inr_getRight : ∀ (x : α ⊕ β) (h : x.isRight), inr (x.getRight h) = x
  | inr _, _ => rfl

@[simp] theorem getLeft?_eq_none_iff {x : α ⊕ β} : x.getLeft? = none ↔ x.isRight := by
  cases x <;> simp only [getLeft?, isRight, eq_self_iff_true, reduceCtorEq]

@[simp] theorem getRight?_eq_none_iff {x : α ⊕ β} : x.getRight? = none ↔ x.isLeft := by
  cases x <;> simp only [getRight?, isLeft, eq_self_iff_true, reduceCtorEq]

theorem eq_left_getLeft_of_isLeft : ∀ {x : α ⊕ β} (h : x.isLeft), x = inl (x.getLeft h)
  | inl _, _ => rfl

@[simp] theorem getLeft_eq_iff (h : x.isLeft) : x.getLeft h = a ↔ x = inl a := by
  cases x <;> simp at h ⊢

theorem eq_right_getRight_of_isRight : ∀ {x : α ⊕ β} (h : x.isRight), x = inr (x.getRight h)
  | inr _, _ => rfl

@[simp] theorem getRight_eq_iff (h : x.isRight) : x.getRight h = b ↔ x = inr b := by
  cases x <;> simp at h ⊢

@[simp] theorem getLeft?_eq_some_iff : x.getLeft? = some a ↔ x = inl a := by
  cases x <;> simp only [getLeft?, Option.some.injEq, inl.injEq, reduceCtorEq]

@[simp] theorem getRight?_eq_some_iff : x.getRight? = some b ↔ x = inr b := by
  cases x <;> simp only [getRight?, Option.some.injEq, inr.injEq, reduceCtorEq]

@[simp] theorem bnot_isLeft (x : α ⊕ β) : !x.isLeft = x.isRight := by cases x <;> rfl

@[simp] theorem isLeft_eq_false {x : α ⊕ β} : x.isLeft = false ↔ x.isRight := by cases x <;> simp

theorem not_isLeft {x : α ⊕ β} : ¬x.isLeft ↔ x.isRight := by simp

@[simp] theorem bnot_isRight (x : α ⊕ β) : !x.isRight = x.isLeft := by cases x <;> rfl

@[simp] theorem isRight_eq_false {x : α ⊕ β} : x.isRight = false ↔ x.isLeft := by cases x <;> simp

theorem not_isRight {x : α ⊕ β} : ¬x.isRight ↔ x.isLeft := by simp

theorem isLeft_iff : x.isLeft ↔ ∃ y, x = Sum.inl y := by cases x <;> simp

theorem isRight_iff : x.isRight ↔ ∃ y, x = Sum.inr y := by cases x <;> simp

end get

theorem inl.inj_iff : (inl a : α ⊕ β) = inl b ↔ a = b := ⟨inl.inj, congrArg _⟩

theorem inr.inj_iff : (inr a : α ⊕ β) = inr b ↔ a = b := ⟨inr.inj, congrArg _⟩

theorem inl_ne_inr : inl a ≠ inr b := nofun

theorem inr_ne_inl : inr b ≠ inl a := nofun

/-! ### `Sum.elim` -/

@[simp] theorem elim_comp_inl (f : α → γ) (g : β → γ) : Sum.elim f g ∘ inl = f :=
  rfl

@[simp] theorem elim_comp_inr (f : α → γ) (g : β → γ) : Sum.elim f g ∘ inr = g :=
  rfl

@[simp] theorem elim_inl_inr : @Sum.elim α β _ inl inr = id :=
  funext fun x => Sum.casesOn x (fun _ => rfl) fun _ => rfl

theorem comp_elim (f : γ → δ) (g : α → γ) (h : β → γ) :
    f ∘ Sum.elim g h = Sum.elim (f ∘ g) (f ∘ h) :=
  funext fun x => Sum.casesOn x (fun _ => rfl) fun _ => rfl

@[simp] theorem elim_comp_inl_inr (f : α ⊕ β → γ) :
    Sum.elim (f ∘ inl) (f ∘ inr) = f :=
  funext fun x => Sum.casesOn x (fun _ => rfl) fun _ => rfl

theorem elim_eq_iff {u u' : α → γ} {v v' : β → γ} :
    Sum.elim u v = Sum.elim u' v' ↔ u = u' ∧ v = v' := by
  simp [funext_iff]

/-! ### `Sum.map` -/

@[simp] theorem map_map (f' : α' → α'') (g' : β' → β'') (f : α → α') (g : β → β') :
    ∀ x : Sum α β, (x.map f g).map f' g' = x.map (f' ∘ f) (g' ∘ g)
  | inl _ => rfl
  | inr _ => rfl

@[simp] theorem map_comp_map (f' : α' → α'') (g' : β' → β'') (f : α → α') (g : β → β') :
    Sum.map f' g' ∘ Sum.map f g = Sum.map (f' ∘ f) (g' ∘ g) :=
  funext <| map_map f' g' f g

@[simp] theorem map_id_id : Sum.map (@id α) (@id β) = id :=
  funext fun x => Sum.recOn x (fun _ => rfl) fun _ => rfl

theorem elim_map {f₁ : α → β} {f₂ : β → ε} {g₁ : γ → δ} {g₂ : δ → ε} {x} :
    Sum.elim f₂ g₂ (Sum.map f₁ g₁ x) = Sum.elim (f₂ ∘ f₁) (g₂ ∘ g₁) x := by
  cases x <;> rfl

theorem elim_comp_map {f₁ : α → β} {f₂ : β → ε} {g₁ : γ → δ} {g₂ : δ → ε} :
    Sum.elim f₂ g₂ ∘ Sum.map f₁ g₁ = Sum.elim (f₂ ∘ f₁) (g₂ ∘ g₁) :=
  funext fun _ => elim_map

@[simp] theorem isLeft_map (f : α → β) (g : γ → δ) (x : α ⊕ γ) :
    isLeft (x.map f g) = isLeft x := by
  cases x <;> rfl

@[simp] theorem isRight_map (f : α → β) (g : γ → δ) (x : α ⊕ γ) :
    isRight (x.map f g) = isRight x := by
  cases x <;> rfl

@[simp] theorem getLeft?_map (f : α → β) (g : γ → δ) (x : α ⊕ γ) :
    (x.map f g).getLeft? = x.getLeft?.map f := by
  cases x <;> rfl

@[simp] theorem getRight?_map (f : α → β) (g : γ → δ) (x : α ⊕ γ) :
    (x.map f g).getRight? = x.getRight?.map g := by cases x <;> rfl

/-! ### `Sum.swap` -/

@[simp] theorem swap_swap (x : α ⊕ β) : swap (swap x) = x := by cases x <;> rfl

@[simp] theorem swap_swap_eq : swap ∘ swap = @id (α ⊕ β) := funext <| swap_swap

@[simp] theorem isLeft_swap (x : α ⊕ β) : x.swap.isLeft = x.isRight := by cases x <;> rfl

@[simp] theorem isRight_swap (x : α ⊕ β) : x.swap.isRight = x.isLeft := by cases x <;> rfl

@[simp] theorem getLeft?_swap (x : α ⊕ β) : x.swap.getLeft? = x.getRight? := by cases x <;> rfl

@[simp] theorem getRight?_swap (x : α ⊕ β) : x.swap.getRight? = x.getLeft? := by cases x <;> rfl

section LiftRel

theorem LiftRel.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ a b, s₁ a b → s₂ a b)
  (h : LiftRel r₁ s₁ x y) : LiftRel r₂ s₂ x y := by
  cases h
  · exact LiftRel.inl (hr _ _ ‹_›)
  · exact LiftRel.inr (hs _ _ ‹_›)

theorem LiftRel.mono_left (hr : ∀ a b, r₁ a b → r₂ a b) (h : LiftRel r₁ s x y) :
    LiftRel r₂ s x y :=
  (h.mono hr) fun _ _ => id

theorem LiftRel.mono_right (hs : ∀ a b, s₁ a b → s₂ a b) (h : LiftRel r s₁ x y) :
    LiftRel r s₂ x y :=
  h.mono (fun _ _ => id) hs

protected theorem LiftRel.swap (h : LiftRel r s x y) : LiftRel s r x.swap y.swap := by
  cases h
  · exact LiftRel.inr ‹_›
  · exact LiftRel.inl ‹_›

@[simp] theorem liftRel_swap_iff : LiftRel s r x.swap y.swap ↔ LiftRel r s x y :=
  ⟨fun h => by rw [← swap_swap x, ← swap_swap y]; exact h.swap, LiftRel.swap⟩

end LiftRel

section Lex

protected theorem LiftRel.lex {a b : α ⊕ β} (h : LiftRel r s a b) : Lex r s a b := by
  cases h
  · exact Lex.inl ‹_›
  · exact Lex.inr ‹_›

theorem liftRel_subrelation_lex : Subrelation (LiftRel r s) (Lex r s) := LiftRel.lex

theorem Lex.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ a b, s₁ a b → s₂ a b) (h : Lex r₁ s₁ x y) :
    Lex r₂ s₂ x y := by
  cases h
  · exact Lex.inl (hr _ _ ‹_›)
  · exact Lex.inr (hs _ _ ‹_›)
  · exact Lex.sep _ _

theorem Lex.mono_left (hr : ∀ a b, r₁ a b → r₂ a b) (h : Lex r₁ s x y) : Lex r₂ s x y :=
  (h.mono hr) fun _ _ => id

theorem Lex.mono_right (hs : ∀ a b, s₁ a b → s₂ a b) (h : Lex r s₁ x y) : Lex r s₂ x y :=
  h.mono (fun _ _ => id) hs

theorem lex_acc_inl (aca : Acc r a) : Acc (Lex r s) (inl a) := by
  induction aca with
  | intro _ _ IH =>
    constructor
    intro y h
    cases h with
    | inl h' => exact IH _ h'

theorem lex_acc_inr (aca : ∀ a, Acc (Lex r s) (inl a)) {b} (acb : Acc s b) :
    Acc (Lex r s) (inr b) := by
  induction acb with
  | intro _ _ IH =>
    constructor
    intro y h
    cases h with
    | inr h' => exact IH _ h'
    | sep => exact aca _

theorem lex_wf (ha : WellFounded r) (hb : WellFounded s) : WellFounded (Lex r s) :=
  have aca : ∀ a, Acc (Lex r s) (inl a) := fun a => lex_acc_inl (ha.apply a)
  ⟨fun x => Sum.recOn x aca fun b => lex_acc_inr aca (hb.apply b)⟩

end Lex

theorem elim_const_const (c : γ) :
    Sum.elim (const _ c : α → γ) (const _ c : β → γ) = const _ c := by
  apply funext
  rintro (_ | _) <;> rfl

@[simp] theorem elim_lam_const_lam_const (c : γ) :
    Sum.elim (fun _ : α => c) (fun _ : β => c) = fun _ => c :=
  Sum.elim_const_const c
