/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

notation, basic datatypes and type classes
-/
prelude
import Init.Core
set_option linter.missingDocs true -- keep it documented

theorem of_eq_true (h : p = True) : p := h ▸ trivial
theorem of_eq_false (h : p = False) : ¬ p := fun hp => False.elim (h.mp hp)

theorem eq_true (h : p) : p = True :=
  propext ⟨fun _ => trivial, fun _ => h⟩

-- Adding this attribute needs `eq_true`.
attribute [simp] cast_heq

theorem eq_false (h : ¬ p) : p = False :=
  propext ⟨fun h' => absurd h' h, fun h' => False.elim h'⟩

theorem eq_false' (h : p → False) : p = False := eq_false h

theorem eq_true_of_decide {p : Prop} [Decidable p] (h : decide p = true) : p = True :=
  eq_true (of_decide_eq_true h)

theorem eq_false_of_decide {p : Prop} {_ : Decidable p} (h : decide p = false) : p = False :=
  eq_false (of_decide_eq_false h)

@[simp] theorem eq_self (a : α) : (a = a) = True := eq_true rfl

theorem implies_congr {p₁ p₂ : Sort u} {q₁ q₂ : Sort v} (h₁ : p₁ = p₂) (h₂ : q₁ = q₂) : (p₁ → q₁) = (p₂ → q₂) :=
  h₁ ▸ h₂ ▸ rfl

theorem iff_congr {p₁ p₂ q₁ q₂ : Prop} (h₁ : p₁ ↔ p₂) (h₂ : q₁ ↔ q₂) : (p₁ ↔ q₁) ↔ (p₂ ↔ q₂) :=
  Iff.of_eq (propext h₁ ▸ propext h₂ ▸ rfl)

theorem implies_dep_congr_ctx {p₁ p₂ q₁ : Prop} (h₁ : p₁ = p₂) {q₂ : p₂ → Prop} (h₂ : (h : p₂) → q₁ = q₂ h) : (p₁ → q₁) = ((h : p₂) → q₂ h) :=
  propext ⟨
    fun hl hp₂ => (h₂ hp₂).mp (hl (h₁.mpr hp₂)),
    fun hr hp₁ => (h₂ (h₁.mp hp₁)).mpr (hr (h₁.mp hp₁))⟩

theorem implies_congr_ctx {p₁ p₂ q₁ q₂ : Prop} (h₁ : p₁ = p₂) (h₂ : p₂ → q₁ = q₂) : (p₁ → q₁) = (p₂ → q₂) :=
  implies_dep_congr_ctx h₁ h₂

theorem forall_congr {α : Sort u} {p q : α → Prop} (h : ∀ a, p a = q a) : (∀ a, p a) = (∀ a, q a) :=
  (funext h : p = q) ▸ rfl

theorem forall_prop_domain_congr {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → Prop}
    (h₁ : p₁ = p₂)
    (h₂ : ∀ a : p₂, q₁ (h₁.substr a) = q₂ a)
    : (∀ a : p₁, q₁ a) = (∀ a : p₂, q₂ a) := by
  subst h₁; simp [← h₂]

theorem forall_prop_congr_dom {p₁ p₂ : Prop} (h : p₁ = p₂) (q : p₁ → Prop) :
    (∀ a : p₁, q a) = (∀ a : p₂, q (h.substr a)) :=
  h ▸ rfl

theorem pi_congr {α : Sort u} {β β' : α → Sort v} (h : ∀ a, β a = β' a) : (∀ a, β a) = ∀ a, β' a :=
  (funext h : β = β') ▸ rfl

theorem let_congr {α : Sort u} {β : Sort v} {a a' : α} {b b' : α → β}
    (h₁ : a = a') (h₂ : ∀ x, b x = b' x) : (let x := a; b x) = (let x := a'; b' x) :=
  h₁ ▸ (funext h₂ : b = b') ▸ rfl

theorem let_val_congr {α : Sort u} {β : Sort v} {a a' : α}
    (b : α → β) (h : a = a') : (let x := a; b x) = (let x := a'; b x) := h ▸ rfl

theorem let_body_congr {α : Sort u} {β : α → Sort v} {b b' : (a : α) → β a}
    (a : α) (h : ∀ x, b x = b' x) : (let x := a; b x) = (let x := a; b' x) :=
  (funext h : b = b') ▸ rfl

@[congr]
theorem ite_congr {x y u v : α} {s : Decidable b} [Decidable c]
    (h₁ : b = c) (h₂ : c → x = u) (h₃ : ¬ c → y = v) : ite b x y = ite c u v := by
  cases Decidable.em c with
  | inl h => rw [if_pos h]; subst b; rw [if_pos h]; exact h₂ h
  | inr h => rw [if_neg h]; subst b; rw [if_neg h]; exact h₃ h

theorem Eq.mpr_prop {p q : Prop} (h₁ : p = q) (h₂ : q)  : p  := h₁ ▸ h₂
theorem Eq.mpr_not  {p q : Prop} (h₁ : p = q) (h₂ : ¬q) : ¬p := h₁ ▸ h₂

@[congr]
theorem dite_congr {_ : Decidable b} [Decidable c]
    {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
    (h₁ : b = c)
    (h₂ : (h : c)  → x (h₁.mpr_prop h) = u h)
    (h₃ : (h : ¬c) → y (h₁.mpr_not h)  = v h) :
    dite b x y = dite c u v := by
  cases Decidable.em c with
  | inl h => rw [dif_pos h]; subst b; rw [dif_pos h]; exact h₂ h
  | inr h => rw [dif_neg h]; subst b; rw [dif_neg h]; exact h₃ h

@[simp] theorem ne_eq (a b : α) : (a ≠ b) = ¬(a = b) := rfl
norm_cast_add_elim ne_eq
@[simp] theorem ite_true (a b : α) : (if True then a else b) = a := rfl
@[simp] theorem ite_false (a b : α) : (if False then a else b) = b := rfl
@[simp] theorem dite_true {α : Sort u} {t : True → α} {e : ¬ True → α} : (dite True t e) = t True.intro := rfl
@[simp] theorem dite_false {α : Sort u} {t : False → α} {e : ¬ False → α} : (dite False t e) = e not_false := rfl
section SimprocHelperLemmas
set_option simprocs false
theorem ite_cond_eq_true {α : Sort u} {c : Prop} {_ : Decidable c} (a b : α) (h : c = True) : (if c then a else b) = a := by simp [h]
theorem ite_cond_eq_false {α : Sort u} {c : Prop} {_ : Decidable c} (a b : α) (h : c = False) : (if c then a else b) = b := by simp [h]
theorem dite_cond_eq_true {α : Sort u} {c : Prop} {_ : Decidable c} {t : c → α} {e : ¬ c → α} (h : c = True) : (dite c t e) = t (of_eq_true h) := by simp [h]
theorem dite_cond_eq_false {α : Sort u} {c : Prop} {_ : Decidable c} {t : c → α} {e : ¬ c → α} (h : c = False) : (dite c t e) = e (of_eq_false h) := by simp [h]
end SimprocHelperLemmas
@[simp] theorem ite_self {α : Sort u} {c : Prop} {d : Decidable c} (a : α) : ite c a a = a := by cases d <;> rfl

@[simp] theorem and_true (p : Prop) : (p ∧ True) = p := propext ⟨(·.1), (⟨·, trivial⟩)⟩
@[simp] theorem true_and (p : Prop) : (True ∧ p) = p := propext ⟨(·.2), (⟨trivial, ·⟩)⟩
instance : Std.LawfulIdentity And True where
  left_id := true_and
  right_id := and_true
@[simp] theorem and_false (p : Prop) : (p ∧ False) = False := eq_false (·.2)
@[simp] theorem false_and (p : Prop) : (False ∧ p) = False := eq_false (·.1)
@[simp] theorem and_self (p : Prop) : (p ∧ p) = p := propext ⟨(·.left), fun h => ⟨h, h⟩⟩
instance : Std.IdempotentOp And := ⟨and_self⟩
@[simp] theorem and_not_self : ¬(a ∧ ¬a) | ⟨ha, hn⟩ => absurd ha hn
@[simp] theorem not_and_self : ¬(¬a ∧ a) := and_not_self ∘ And.symm
@[simp] theorem and_imp : (a ∧ b → c) ↔ (a → b → c) := ⟨fun h ha hb => h ⟨ha, hb⟩, fun h ⟨ha, hb⟩ => h ha hb⟩
@[simp] theorem not_and : ¬(a ∧ b) ↔ (a → ¬b) := and_imp
@[simp] theorem or_self (p : Prop) : (p ∨ p) = p := propext ⟨fun | .inl h | .inr h => h, .inl⟩
instance : Std.IdempotentOp Or := ⟨or_self⟩
@[simp] theorem or_true (p : Prop) : (p ∨ True) = True := eq_true (.inr trivial)
@[simp] theorem true_or (p : Prop) : (True ∨ p) = True := eq_true (.inl trivial)
@[simp] theorem or_false (p : Prop) : (p ∨ False) = p := propext ⟨fun (.inl h) => h, .inl⟩
@[simp] theorem false_or (p : Prop) : (False ∨ p) = p := propext ⟨fun (.inr h) => h, .inr⟩
instance : Std.LawfulIdentity Or False where
  left_id := false_or
  right_id := or_false
@[simp] theorem iff_self (p : Prop) : (p ↔ p) = True := eq_true .rfl
@[simp] theorem iff_true (p : Prop) : (p ↔ True) = p := propext ⟨(·.2 trivial), fun h => ⟨fun _ => trivial, fun _ => h⟩⟩
@[simp] theorem true_iff (p : Prop) : (True ↔ p) = p := propext ⟨(·.1 trivial), fun h => ⟨fun _ => h, fun _ => trivial⟩⟩
@[simp] theorem iff_false (p : Prop) : (p ↔ False) = ¬p := propext ⟨(·.1), (⟨·, False.elim⟩)⟩
@[simp] theorem false_iff (p : Prop) : (False ↔ p) = ¬p := propext ⟨(·.2), (⟨False.elim, ·⟩)⟩
@[simp] theorem false_implies (p : Prop) : (False → p) = True := eq_true False.elim
@[simp] theorem forall_false (p : False → Prop) : (∀ h : False, p h) = True := eq_true (False.elim ·)
@[simp] theorem implies_true (α : Sort u) : (α → True) = True := eq_true fun _ => trivial
@[simp] theorem true_implies (p : Prop) : (True → p) = p := propext ⟨(· trivial), (fun _ => ·)⟩
@[simp] theorem not_false_eq_true : (¬ False) = True := eq_true False.elim
@[simp] theorem not_true_eq_false : (¬ True) = False := by decide

@[simp] theorem not_iff_self : ¬(¬a ↔ a) | H => iff_not_self H.symm
attribute [simp] iff_not_self

/-! ## and -/

theorem and_congr_right (h : a → (b ↔ c)) : a ∧ b ↔ a ∧ c :=
  Iff.intro (fun ⟨ha, hb⟩ => And.intro ha ((h ha).mp hb))
            (fun ⟨ha, hb⟩ => And.intro ha ((h ha).mpr hb))
theorem and_congr_left (h : c → (a ↔ b)) : a ∧ c ↔ b ∧ c :=
  Iff.trans and_comm (Iff.trans (and_congr_right h) and_comm)

theorem and_assoc : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
  Iff.intro (fun ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, hb, hc⟩)
            (fun ⟨ha, hb, hc⟩ => ⟨⟨ha, hb⟩, hc⟩)
instance : Std.Associative And := ⟨fun _ _ _ => propext and_assoc⟩

@[simp] theorem and_self_left  : a ∧ (a ∧ b) ↔ a ∧ b := by rw [←propext and_assoc, and_self]
@[simp] theorem and_self_right : (a ∧ b) ∧ b ↔ a ∧ b := by rw [ propext and_assoc, and_self]

@[simp] theorem and_congr_right_iff : (a ∧ b ↔ a ∧ c) ↔ (a → (b ↔ c)) :=
  Iff.intro (fun h ha => by simp [ha] at h; exact h) and_congr_right
@[simp] theorem and_congr_left_iff : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) := by
  rw [@and_comm _ c, @and_comm _ c, ← and_congr_right_iff]

theorem and_iff_left_of_imp  (h : a → b) : (a ∧ b) ↔ a := Iff.intro And.left (fun ha => And.intro ha (h ha))
theorem and_iff_right_of_imp (h : b → a) : (a ∧ b) ↔ b := Iff.trans And.comm (and_iff_left_of_imp h)

@[simp] theorem and_iff_left_iff_imp  : ((a ∧ b) ↔ a) ↔ (a → b) := Iff.intro (And.right ∘ ·.mpr) and_iff_left_of_imp
@[simp] theorem and_iff_right_iff_imp : ((a ∧ b) ↔ b) ↔ (b → a) := Iff.intro (And.left ∘ ·.mpr) and_iff_right_of_imp

@[simp] theorem iff_self_and : (p ↔ p ∧ q) ↔ (p → q) := by rw [@Iff.comm p, and_iff_left_iff_imp]
@[simp] theorem iff_and_self : (p ↔ q ∧ p) ↔ (p → q) := by rw [and_comm, iff_self_and]

/-! ## or -/

theorem Or.imp (f : a → c) (g : b → d) (h : a ∨ b) : c ∨ d := h.elim (inl ∘ f) (inr ∘ g)
theorem Or.imp_left (f : a → b) : a ∨ c → b ∨ c := .imp f id
theorem Or.imp_right (f : b → c) : a ∨ b → a ∨ c := .imp id f

theorem or_assoc : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
  Iff.intro (.rec (.imp_right .inl) (.inr ∘ .inr))
            (.rec (.inl ∘ .inl) (.imp_left .inr))
instance : Std.Associative Or := ⟨fun _ _ _ => propext or_assoc⟩

@[simp] theorem or_self_left  : a ∨ (a ∨ b) ↔ a ∨ b := by rw [←propext or_assoc, or_self]
@[simp] theorem or_self_right : (a ∨ b) ∨ b ↔ a ∨ b := by rw [ propext or_assoc, or_self]

theorem or_iff_right_of_imp (ha : a → b) : (a ∨ b) ↔ b := Iff.intro (Or.rec ha id) .inr
theorem or_iff_left_of_imp  (hb : b → a) : (a ∨ b) ↔ a  := Iff.intro (Or.rec id hb) .inl

@[simp] theorem or_iff_left_iff_imp  : (a ∨ b ↔ a) ↔ (b → a) := Iff.intro (·.mp ∘ Or.inr) or_iff_left_of_imp
@[simp] theorem or_iff_right_iff_imp : (a ∨ b ↔ b) ↔ (a → b) := by rw [or_comm, or_iff_left_iff_imp]

@[simp] theorem iff_self_or {a b : Prop} : (a ↔ a ∨ b) ↔ (b → a) :=
  propext (@Iff.comm _ a) ▸ @or_iff_left_iff_imp a b
@[simp] theorem iff_or_self {a b : Prop} : (b ↔ a ∨ b) ↔ (a → b) :=
  propext (@Iff.comm _ b) ▸ @or_iff_right_iff_imp a b

/-# Bool -/

@[simp] theorem Bool.or_false (b : Bool) : (b || false) = b  := by cases b <;> rfl
@[simp] theorem Bool.or_true (b : Bool) : (b || true) = true := by cases b <;> rfl
@[simp] theorem Bool.false_or (b : Bool) : (false || b) = b  := by cases b <;> rfl
instance : Std.LawfulIdentity (· || ·) false where
  left_id := Bool.false_or
  right_id := Bool.or_false
@[simp] theorem Bool.true_or (b : Bool) : (true || b) = true := by cases b <;> rfl
@[simp] theorem Bool.or_self (b : Bool) : (b || b) = b       := by cases b <;> rfl
instance : Std.IdempotentOp (· || ·) := ⟨Bool.or_self⟩
@[simp] theorem Bool.or_eq_true (a b : Bool) : ((a || b) = true) = (a = true ∨ b = true) := by
  cases a <;> cases b <;> decide

@[simp] theorem Bool.and_false (b : Bool) : (b && false) = false := by cases b <;> rfl
@[simp] theorem Bool.and_true (b : Bool) : (b && true) = b       := by cases b <;> rfl
@[simp] theorem Bool.false_and (b : Bool) : (false && b) = false := by cases b <;> rfl
@[simp] theorem Bool.true_and (b : Bool) : (true && b) = b       := by cases b <;> rfl
instance : Std.LawfulIdentity (· && ·) true where
  left_id := Bool.true_and
  right_id := Bool.and_true
@[simp] theorem Bool.and_self (b : Bool) : (b && b) = b          := by cases b <;> rfl
instance : Std.IdempotentOp (· && ·) := ⟨Bool.and_self⟩
@[simp] theorem Bool.and_eq_true (a b : Bool) : ((a && b) = true) = (a = true ∧ b = true) := by
  cases a <;> cases b <;> decide

theorem Bool.and_assoc (a b c : Bool) : (a && b && c) = (a && (b && c)) := by
  cases a <;> cases b <;> cases c <;> decide
instance : Std.Associative (· && ·) := ⟨Bool.and_assoc⟩
theorem Bool.or_assoc (a b c : Bool) : (a || b || c) = (a || (b || c)) := by
  cases a <;> cases b <;> cases c <;> decide
instance : Std.Associative (· || ·) := ⟨Bool.or_assoc⟩

@[simp] theorem Bool.not_not (b : Bool) : (!!b) = b := by cases b <;> rfl
@[simp] theorem Bool.not_true  : (!true) = false := by decide
@[simp] theorem Bool.not_false : (!false) = true := by decide
@[simp] theorem beq_true  (b : Bool) : (b == true)  =  b := by cases b <;> rfl
@[simp] theorem beq_false (b : Bool) : (b == false) = !b := by cases b <;> rfl


/--
We move `!` from the left hand side of an equality to the right hand side.
This helps confluence, and also helps combining pairs of `!`s.
-/
@[simp] theorem Bool.not_eq_eq_eq_not {a b : Bool} : ((!a) = b) ↔ (a = !b) := by
  cases a <;> cases b <;> simp

@[simp] theorem Bool.not_eq_not {a b : Bool} : ¬a = !b ↔ a = b := by
  cases a <;> cases b <;> simp
theorem Bool.not_not_eq {a b : Bool} : ¬(!a) = b ↔ a = b := by simp

theorem Bool.not_eq_true'  (b : Bool) : ((!b) = true) = (b = false) := by simp
theorem Bool.not_eq_false' (b : Bool) : ((!b) = false) = (b = true) := by simp

@[simp] theorem Bool.not_eq_true (b : Bool) : (¬(b = true)) = (b = false) := by cases b <;> decide
@[simp] theorem Bool.not_eq_false (b : Bool) : (¬(b = false)) = (b = true) := by cases b <;> decide

@[simp] theorem decide_eq_true_eq [Decidable p] : (decide p = true) = p :=
  propext <| Iff.intro of_decide_eq_true decide_eq_true
@[simp] theorem decide_eq_false_iff_not {_ : Decidable p} : (decide p = false) ↔ ¬p :=
  ⟨of_decide_eq_false, decide_eq_false⟩

@[simp] theorem decide_not [g : Decidable p] [h : Decidable (Not p)] : decide (Not p) = !(decide p) := by
  cases g <;> (rename_i gp; simp [gp])
theorem not_decide_eq_true [h : Decidable p] : ((!decide p) = true) = ¬ p := by simp

@[simp] theorem heq_eq_eq (a b : α) : HEq a b = (a = b) := propext <| Iff.intro eq_of_heq heq_of_eq

@[simp] theorem cond_true (a b : α) : cond true a b = a := rfl
@[simp] theorem cond_false (a b : α) : cond false a b = b := rfl

@[simp] theorem beq_self_eq_true [BEq α] [LawfulBEq α] (a : α) : (a == a) = true := LawfulBEq.rfl
theorem beq_self_eq_true' [DecidableEq α] (a : α) : (a == a) = true := by simp

@[simp] theorem bne_self_eq_false [BEq α] [LawfulBEq α] (a : α) : (a != a) = false := by simp [bne]
theorem bne_self_eq_false' [DecidableEq α] (a : α) : (a != a) = false := by simp

set_option linter.missingDocs false in
@[deprecated decide_false (since := "2024-11-05")] abbrev decide_False := decide_false
set_option linter.missingDocs false in
@[deprecated decide_true  (since := "2024-11-05")] abbrev decide_True  := decide_true

@[simp] theorem bne_iff_ne [BEq α] [LawfulBEq α] {a b : α} : a != b ↔ a ≠ b := by
  simp [bne]; rw [← beq_iff_eq (a := a) (b := b)]; simp [-beq_iff_eq]

/-
Added for critical pair for `¬((a != b) = true)`

1. `(a != b) = false` via `Bool.not_eq_true`
2. `¬(a ≠ b)` via `bne_iff_ne`

These will both normalize to `a = b` with the first via `bne_eq_false_iff_eq`.
-/
@[simp] theorem beq_eq_false_iff_ne [BEq α] [LawfulBEq α] {a b : α} : (a == b) = false ↔ a ≠ b := by
  rw [ne_eq, ← beq_iff_eq (a := a) (b := b)]
  cases a == b <;> decide

@[simp] theorem bne_eq_false_iff_eq [BEq α] [LawfulBEq α] {a b : α} : (a != b) = false ↔ a = b := by
  rw [bne, ← beq_iff_eq (a := a) (b := b)]
  cases a == b <;> decide

theorem Bool.beq_to_eq (a b : Bool) : (a == b) = (a = b) := by simp
theorem Bool.not_beq_to_not_eq (a b : Bool) : (!(a == b)) = ¬(a = b) := by simp

/- # Nat -/

@[simp] theorem Nat.le_zero_eq (a : Nat) : (a ≤ 0) = (a = 0) :=
  propext ⟨fun h => Nat.le_antisymm h (Nat.zero_le ..), fun h => by rw [h]; decide⟩
