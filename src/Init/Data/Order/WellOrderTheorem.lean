/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Init.Data.Order.Ord
import Init.Classical
import Init.RCases
import Init.Data.Order.Lemmas
import Init.WFTactics
import Init.ByCases
import all Init.Internal.Order.Basic

inductive PreOrdinal.{u} where
  | bsup (α : Sort u) (f : α → PreOrdinal)

protected def PreOrdinal.le (a b : PreOrdinal.{u}) : Prop :=
  match a, b with
  | .bsup α f, .bsup β g => ∀ x : α, ∃ y : β, (f x).le (g y)

protected def PreOrdinal.lt (a b : PreOrdinal.{u}) : Prop :=
  match a, b with
  | .bsup α f, .bsup β g => ∃ y : β, ∀ x : α, (f x).lt (g y)

instance : LE PreOrdinal.{u} where
  le := PreOrdinal.le

instance : LT PreOrdinal.{u} where
  lt := PreOrdinal.lt

namespace PreOrdinal

@[simp]
theorem bsup_le_iff {α : Sort u} {f : α → PreOrdinal} {y : PreOrdinal} :
    bsup α f ≤ y ↔ ∀ x, f x < y := by
  induction y generalizing α f with | bsup β g ih
  change (∀ x : α, ∃ y : β, f x ≤ g y) ↔ _
  refine forall_congr' fun a => ?_
  generalize f a = fa
  rcases fa with ⟨α', f'⟩
  change _ ↔ (∃ y : β, ∀ x : α', f' x < g y)
  simp [ih]

@[simp, grind =]
theorem lt_bsup_iff {α : Sort u} {f : α → PreOrdinal} {y : PreOrdinal} :
    y < bsup α f ↔ ∃ x, y ≤ f x := by
  rcases y with ⟨β, g⟩
  change (∃ y : α, ∀ x : β, g x < f y) ↔ _
  simp

instance : Std.IsLinearPreorder PreOrdinal.{u} where
  le_refl x := by
    induction x with | bsup α f ih
    simp only [bsup_le_iff, lt_bsup_iff]
    exact fun x => ⟨x, ih x⟩
  le_trans a b c hab hbc := by
    induction a generalizing b c with | bsup α f ih
    rcases b with ⟨β, g⟩
    rcases c with ⟨γ, h⟩
    simp only [bsup_le_iff, lt_bsup_iff] at hab hbc ⊢
    intro x
    obtain ⟨y, hy⟩ := hab x
    obtain ⟨z, hz⟩ := hbc y
    exact ⟨z, ih x (g y) (h z) hy hz⟩
  le_total x y := by
    induction x generalizing y with | bsup α f ih
    rcases y with ⟨β, g⟩
    simp only [bsup_le_iff, lt_bsup_iff]
    false_or_by_contra; rename_i h
    simp only [not_or, Classical.not_forall, not_exists] at h
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h
    exact absurd ((ih x (g y)).resolve_left (hx y)) (hy x)

instance : Std.LawfulOrderLT PreOrdinal.{u} where
  lt_iff x y := by
    suffices x < y ↔ ¬ y ≤ x by simp [this, eq_true Std.le_of_not_ge]
    induction x generalizing y with | bsup α f ih
    rcases y with ⟨β, g⟩
    simp [ih _ (g _)]

end PreOrdinal

def Ordinal.{u} : Type u :=
  @Quotient PreOrdinal.{u} {
    r a b := a ≤ b ∧ b ≤ a
    iseqv := {
      refl := by simp
      symm h := h.symm
      trans h h' := ⟨Std.le_trans h.1 h'.1, Std.le_trans h'.2 h.2⟩
    }
  }

instance : LE Ordinal.{u} where
  le := Quotient.lift₂ (· ≤ ·) fun a₁ b₁ a₂ b₂ (h₁ : _ ∧ _) (h₂ : _ ∧ _) => by
    apply propext
    exact ⟨fun h => Std.le_trans (Std.le_trans h₁.2 h) h₂.1,
      fun h => Std.le_trans (Std.le_trans h₁.1 h) h₂.2⟩

instance : LT Ordinal.{u} where
  lt := Quotient.lift₂ (· < ·) fun a₁ b₁ a₂ b₂ (h₁ : _ ∧ _) (h₂ : _ ∧ _) => by
    apply propext
    exact ⟨fun h => Std.lt_of_lt_of_le (Std.lt_of_le_of_lt h₁.2 h) h₂.1,
      fun h => Std.lt_of_lt_of_le (Std.lt_of_le_of_lt h₁.1 h) h₂.2⟩

instance : Std.IsLinearOrder Ordinal.{u} where
  le_refl := Quotient.ind Std.le_refl
  le_trans a b c := Quotient.inductionOn₃ a b c fun _ _ _ => Std.le_trans (α := PreOrdinal.{u})
  le_antisymm := Quotient.ind₂ fun a b (h : a ≤ b) (h' : b ≤ a) => Quotient.sound ⟨h, h'⟩
  le_total := Quotient.ind₂ (@Std.le_total _ _ _)

instance : Std.LawfulOrderLT Ordinal.{u} where
  lt_iff := Quotient.ind₂ fun _ _ => Std.lt_iff_le_and_not_ge (α := PreOrdinal.{u})

noncomputable def Ordinal.bsup (α : Sort u) (f : α → Ordinal.{u}) : Ordinal.{u} :=
  .mk _ (.bsup α fun x => (f x).exists_rep.choose)

@[simp]
theorem Ordinal.bsup_le_iff {α : Sort u} {f : α → Ordinal.{u}} {x : Ordinal.{u}} :
    bsup α f ≤ x ↔ ∀ a, f a < x := by
  induction x using Quotient.inductionOn with | _ x
  refine Iff.trans PreOrdinal.bsup_le_iff ?_
  refine forall_congr' fun a => ?_
  change (show Ordinal.{u} from .mk _ _) < (show Ordinal.{u} from .mk _ _) ↔ _
  simp [(f a).exists_rep.choose_spec]

@[simp]
theorem Ordinal.lt_bsup_iff {α : Sort u} {f : α → Ordinal.{u}} {x : Ordinal.{u}} :
    x < bsup α f ↔ ∃ a, x ≤ f a := by
  classical
  rw [← Decidable.not_iff_not]
  simp [Std.not_lt, Std.not_le]

@[elab_as_elim]
theorem Ordinal.bsup_ind {motive : Ordinal.{u} → Prop}
    (bsup : (α : Sort u) → (f : α → Ordinal.{u}) →
      (f_ih : ∀ a, motive (f a)) → motive (bsup α f))
    (t : Ordinal.{u}) : motive t := by
  induction t using Quotient.inductionOn with | _ x
  induction x with | _ α f ih
  refine cast (congrArg motive ?_) (bsup α (fun x => .mk _ (f x)) ih)
  apply Quotient.sound
  have le_iff (x y : PreOrdinal.{u}) :
    (show Ordinal.{u} from .mk _ x) ≤ (show Ordinal.{u} from .mk _ y) ↔ x ≤ y := Iff.rfl
  constructor
  · simp only [PreOrdinal.bsup_le_iff, PreOrdinal.lt_bsup_iff]
    intro x
    exists x
    rw [← le_iff, (Quotient.exists_rep _).choose_spec]
    apply Std.le_refl
  · simp only [PreOrdinal.bsup_le_iff, PreOrdinal.lt_bsup_iff]
    intro x
    exists x
    rw [← le_iff, (Quotient.exists_rep _).choose_spec]
    apply Std.le_refl

theorem Ordinal.wellFounded_lt : WellFounded (· < · : Ordinal.{u} → _) := by
  constructor
  intro x
  suffices ∀ y, y ≤ x → Acc (· < ·) y from this x (Std.le_refl x)
  intro y hyx
  induction x using bsup_ind generalizing y with | _ α f ih
  constructor
  intro z hzy
  replace hzy := Std.lt_of_lt_of_le hzy hyx
  rw [lt_bsup_iff] at hzy
  obtain ⟨a, ha⟩ := hzy
  exact ih a z ha

instance : WellFoundedRelation Ordinal.{u} where
  rel := LT.lt
  wf := Ordinal.wellFounded_lt

inductive POption (α : Sort u) where
  | none
  | some (x : α)

noncomputable def embed {α : Sort u} (x : Ordinal.{u}) : POption α :=
  open scoped Classical in
  if h : ∃ a : α, (∀ y, (h : y < x) → embed y ≠ .some a) then
    .some h.choose
  else
    .none
termination_by x

theorem le_of_embed_eq_some {x : α} {o₁ o₂ : Ordinal.{u}}
    (h₁ : embed o₁ = .some x) (h₂ : embed o₂ = .some x) : o₁ ≤ o₂ := by
  rw [← Std.not_lt]
  intro h
  rw [embed] at h₁
  split at h₁
  · rename_i h'
    cases h₁
    have := h'.choose_spec o₂ h
    contradiction
  · contradiction

theorem embed_injective {x : α} {o₁ o₂ : Ordinal.{u}}
    (h₁ : embed o₁ = .some x) (h₂ : embed o₂ = .some x) : o₁ = o₂ :=
  Std.le_antisymm (le_of_embed_eq_some h₁ h₂) (le_of_embed_eq_some h₂ h₁)

theorem embed_surjective : ∀ x : α, ∃ y, embed y = .some x := by
  classical
  intro x
  false_or_by_contra; rename_i h
  rw [not_exists] at h
  let o := Ordinal.bsup α fun x => if h : ∃ y, embed y = .some x then h.choose else .bsup PEmpty nofun
  have : (embed o : POption α) ≠ .none := by
    rw [embed]
    simp only [ne_eq, dite_eq_right_iff, reduceCtorEq, imp_false, not_exists, not_imp,
      Classical.not_forall, not_and, Classical.not_not]
    exists x
    simp [h]
  replace : ∃ a : α, embed o = .some a := by revert this; cases embed o <;> simp
  obtain ⟨a, ha⟩ := this
  have : o < o := by
    rw [Ordinal.lt_bsup_iff]
    exists a
    rw [dite_eq_left ⟨o, ha⟩]
    simp [embed_injective (⟨o, ha⟩ : ∃ y, embed y = POption.some a).choose_spec ha]
  exact Std.lt_irrefl this

theorem exists_wellOrder (α : Sort u) :
    ∃ r : α → α → Prop, WellFounded r ∧ (∀ a b, r a b ∨ a = b ∨ r b a) ∧ (∀ {a b c}, r a b → r b c → r a c) ∧ (∀ a, ¬ r a a) := by
  exists fun a b => (embed_surjective a).choose < (embed_surjective b).choose
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact InvImage.wf (fun a => (embed_surjective a).choose) Ordinal.wellFounded_lt
  · intro a b
    obtain lt | eq | gt := Std.lt_trichotomy (embed_surjective a).choose (embed_surjective b).choose
    · left; assumption
    · right; left
      have h₁ := (embed_surjective a).choose_spec
      have h₂ := (embed_surjective b).choose_spec
      rw [eq] at h₁
      simp_all
    · right; right; assumption
  · intro a b c
    exact Std.lt_trans
  · intro a
    exact Std.lt_irrefl

/-- Every type has a well-order -/
public theorem Std.exists_ord_transOrd_and_lawfulEqOrd (α : Type u) :
    ∃ _ : Ord α, Std.TransOrd α ∧ Std.LawfulEqOrd α ∧
      WellFounded (fun a b : α => compare a b = .lt) := by
  classical
  obtain ⟨r, wf, total, trans, irrefl⟩ := exists_wellOrder α
  let lt : LT α := ⟨r⟩
  let le : LE α := ⟨fun a b => ¬ r b a⟩
  let ord : Ord α := ⟨fun a b => compareOfLessAndEq a b⟩
  exists ord
  have : Std.TransOrd α := by
    refine Std.TransOrd.compareOfLessAndEq_of_lt_trans_of_lt_iff ?_ ?_
    · apply trans
    · intro x y
      constructor
      · intro h
        exact ⟨fun h' => irrefl _ (trans h h'), fun | rfl => irrefl _ h⟩
      · intro ⟨h, h'⟩
        exact (total y x).resolve_left h |>.resolve_left h'.symm
  have : Std.LawfulEqOrd α := by
    constructor
    intro a b
    exact compareOfLessAndEq_eq_eq irrefl Classical.not_not |>.mp
  refine ⟨‹_›, ‹_›, ?_⟩
  subst ord lt
  simp [· < ·, wf]

def F (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => f k * 2

def factorial : Nat → Nat := (2 ^ ·)

theorem F_factorial : F factorial = factorial := funext (Nat.rec rfl fun _ _ => rfl)

axiom not_intro : ¬ P → P

theorem factorial_ind {motive : (Nat → Nat) → Prop}
    (thing : ∀ x, motive x → motive (F x)) :
    motive (F factorial) := by
  impossible by
  intro h
  specialize @h fun f => ∃ M, ∀ n₁ n₂, M ≤ n₁ → M ≤ n₂ → f n₁ = f n₂
  specialize @h ?_
  · intro x hx
    obtain ⟨M, hM⟩ := hx
    exists M + 1
    intro n₁ n₂ h₁ h₂
    unfold F
    let n₁ + 1 := n₁
    let n₂ + 1 := n₂
    simp only [Nat.add_le_add_iff_right] at h₁ h₂
    simp [hM _ _ h₁ h₂]
  · obtain ⟨M, hM⟩ := h
    specialize hM (M + 1) (M + 2) (by simp) (by simp)
    simp [factorial, F, ← Nat.pow_succ, Nat.pow_right_inj] at hM

theorem refl_wf (r : α × α → α × α → Prop) (hr : WellFounded r)
    (f : (x : α × α) → (∀ y, r y x → Ordering) → Ordering)
    (H : ∀ x F, (∀ y hy, F (y, y) hy = .eq) → f (x, x) F = .eq) :
    ∀ a, WellFounded.fix hr f (a, a) = .eq := by
  have := InvImage.wf (fun a => (a, a)) hr
  intro a
  induction a using this.induction with | _ x hx
  rw [WellFounded.fix_eq]
  apply H
  exact hx

def GoodFixpoint (F : α → α) (bot : α) (x : α) : Prop :=
    -- if there is a fixpoint with an induction principle, `f` is a fixpoint
  ((∃ x, F x = x ∧ (∀ P : α → Prop, (∀ x, P x → P (F x)) → P x)) → F x = x) ∧
  -- `f` has every property of `bot` that is preserved by `F`
  (∀ P : α → Prop, P bot → (∀ x, P x → P (F x)) → P x)

/-
def GoodFixpoint (F : (α → α → Ordering) → (α → α → Ordering))
    (f : α → α → Ordering) : Prop :=
    -- if there is a fixpoint, `f` is a fixpoint
  ((∃ x, F x = x) → F f = f) ∧
  -- `f` has every property of a linear order that is preserved by `F`
  (∀ P : (α → α → Ordering) → Prop, (∀ cmp, Std.TransCmp cmp → Std.LawfulEqCmp cmp → P cmp) →
    (∀ x, P x → P (F x)) → P f)
-/

instance (F : α → α) (bot : α) :
    Nonempty (Subtype (GoodFixpoint F bot)) := by
  let : Lean.Order.CCPO α := inferInstanceAs (Lean.Order.CCPO (Lean.Order.FlatOrder bot))
  by_cases hmono : Lean.Order.monotone F
  · refine ⟨Lean.Order.fix F hmono, fun _ => (Lean.Order.fix_eq hmono).symm, ?_⟩
    intro P hP hPF
    apply Lean.Order.fix_induct
    · apply Lean.Order.admissible_flatOrder
      exact hP
    · exact hPF
  · by_cases hF : ∃ x, F x = x
    · obtain ⟨x, hx⟩ := hF
      refine ⟨x, fun _ => hx, fun P hP hPF => ?_⟩

    simp [Lean.Order.monotone] at hmono
    obtain ⟨x, f, _ | _, h'⟩ := hmono
    · have : F bot = bot := by
        sorry
    · exact absurd .refl h'

local instance : Nonempty { f : α → α → Ordering //
        -- if there is a fixpoint, `f` is a fixpoint
        ((∃ x, F x = x) → F f = f) ∧
        -- `f` has every property of a linear order that is preserved by `F`
        (∀ P : (α → α → Ordering) → Prop, (∀ cmp, Std.TransCmp cmp → Std.LawfulEqCmp cmp → P cmp) →
          (∀ x, P x → P (F x)) → P f) }

partial def ordFixAux (F : (α → α → Ordering) → (α → α → Ordering)) :
    { f : α → α → Ordering //
        -- if there is a fixpoint, `f` is a fixpoint
        ((∃ x, F x = x) → F f = f) ∧
        -- `f` has every property of a linear order that is preserved by `F`
        (∀ P : (α → α → Ordering) → Prop, (∀ cmp, Std.TransCmp cmp → Std.LawfulEqCmp cmp → P cmp) →
          (∀ x, P x → P (F x)) → P f) } :=
  have x := ordFixAux F
  ⟨F x.1, fun h => by rw [x.2.1 h, x.2.1 h], fun P hP hPF => hPF _ (x.2.2 P hP hPF)⟩
