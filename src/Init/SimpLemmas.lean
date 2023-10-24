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

theorem eq_true (h : p) : p = True :=
  propext ⟨fun _ => trivial, fun _ => h⟩

theorem eq_false (h : ¬ p) : p = False :=
  propext ⟨fun h' => absurd h' h, fun h' => False.elim h'⟩

theorem eq_false' (h : p → False) : p = False := eq_false h

theorem eq_true_of_decide {p : Prop} {_ : Decidable p} (h : decide p = true) : p = True :=
  eq_true (of_decide_eq_true h)

theorem eq_false_of_decide {p : Prop} {_ : Decidable p} (h : decide p = false) : p = False :=
  eq_false (of_decide_eq_false h)

@[simp] theorem eq_self (a : α) : (a = a) = True := eq_true rfl

theorem implies_congr {p₁ p₂ : Sort u} {q₁ q₂ : Sort v} (h₁ : p₁ = p₂) (h₂ : q₁ = q₂) : (p₁ → q₁) = (p₂ → q₂) :=
  h₁ ▸ h₂ ▸ rfl

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
@[simp] theorem ite_true (a b : α) : (if True then a else b) = a := rfl
@[simp] theorem ite_false (a b : α) : (if False then a else b) = b := rfl
@[simp] theorem dite_true {α : Sort u} {t : True → α} {e : ¬ True → α} : (dite True t e) = t True.intro := rfl
@[simp] theorem dite_false {α : Sort u} {t : False → α} {e : ¬ False → α} : (dite False t e) = e not_false := rfl
@[simp] theorem ite_self {α : Sort u} {c : Prop} {d : Decidable c} (a : α) : ite c a a = a := by cases d <;> rfl
@[simp] theorem and_self (p : Prop) : (p ∧ p) = p := propext ⟨(·.1), fun h => ⟨h, h⟩⟩
@[simp] theorem and_true (p : Prop) : (p ∧ True) = p := propext ⟨(·.1), (⟨·, trivial⟩)⟩
@[simp] theorem true_and (p : Prop) : (True ∧ p) = p := propext ⟨(·.2), (⟨trivial, ·⟩)⟩
@[simp] theorem and_false (p : Prop) : (p ∧ False) = False := eq_false (·.2)
@[simp] theorem false_and (p : Prop) : (False ∧ p) = False := eq_false (·.1)
@[simp] theorem or_self (p : Prop) : (p ∨ p) = p := propext ⟨fun | .inl h | .inr h => h, .inl⟩
@[simp] theorem or_true (p : Prop) : (p ∨ True) = True := eq_true (.inr trivial)
@[simp] theorem true_or (p : Prop) : (True ∨ p) = True := eq_true (.inl trivial)
@[simp] theorem or_false (p : Prop) : (p ∨ False) = p := propext ⟨fun (.inl h) => h, .inl⟩
@[simp] theorem false_or (p : Prop) : (False ∨ p) = p := propext ⟨fun (.inr h) => h, .inr⟩
@[simp] theorem iff_self (p : Prop) : (p ↔ p) = True := eq_true .rfl
@[simp] theorem iff_true (p : Prop) : (p ↔ True) = p := propext ⟨(·.2 trivial), fun h => ⟨fun _ => trivial, fun _ => h⟩⟩
@[simp] theorem true_iff (p : Prop) : (True ↔ p) = p := propext ⟨(·.1 trivial), fun h => ⟨fun _ => h, fun _ => trivial⟩⟩
@[simp] theorem iff_false (p : Prop) : (p ↔ False) = ¬p := propext ⟨(·.1), (⟨·, False.elim⟩)⟩
@[simp] theorem false_iff (p : Prop) : (False ↔ p) = ¬p := propext ⟨(·.2), (⟨False.elim, ·⟩)⟩
@[simp] theorem false_implies (p : Prop) : (False → p) = True := eq_true False.elim
@[simp] theorem implies_true (α : Sort u) : (α → True) = True := eq_true fun _ => trivial
@[simp] theorem true_implies (p : Prop) : (True → p) = p := propext ⟨(· trivial), (fun _ => ·)⟩
@[simp] theorem not_false_eq_true : (¬ False) = True := eq_true False.elim

@[simp] theorem Bool.or_false (b : Bool) : (b || false) = b  := by cases b <;> rfl
@[simp] theorem Bool.or_true (b : Bool) : (b || true) = true := by cases b <;> rfl
@[simp] theorem Bool.false_or (b : Bool) : (false || b) = b  := by cases b <;> rfl
@[simp] theorem Bool.true_or (b : Bool) : (true || b) = true := by cases b <;> rfl
@[simp] theorem Bool.or_self (b : Bool) : (b || b) = b       := by cases b <;> rfl
@[simp] theorem Bool.or_eq_true (a b : Bool) : ((a || b) = true) = (a = true ∨ b = true) := by
  cases a <;> cases b <;> decide

@[simp] theorem Bool.and_false (b : Bool) : (b && false) = false := by cases b <;> rfl
@[simp] theorem Bool.and_true (b : Bool) : (b && true) = b       := by cases b <;> rfl
@[simp] theorem Bool.false_and (b : Bool) : (false && b) = false := by cases b <;> rfl
@[simp] theorem Bool.true_and (b : Bool) : (true && b) = b       := by cases b <;> rfl
@[simp] theorem Bool.and_self (b : Bool) : (b && b) = b          := by cases b <;> rfl
@[simp] theorem Bool.and_eq_true (a b : Bool) : ((a && b) = true) = (a = true ∧ b = true) := by
  cases a <;> cases b <;> decide

theorem Bool.and_assoc (a b c : Bool) : (a && b && c) = (a && (b && c)) := by
  cases a <;> cases b <;> cases c <;> decide
theorem Bool.or_assoc (a b c : Bool) : (a || b || c) = (a || (b || c)) := by
  cases a <;> cases b <;> cases c <;> decide

@[simp] theorem Bool.not_not (b : Bool) : (!!b) = b := by cases b <;> rfl
@[simp] theorem Bool.not_true  : (!true) = false := by decide
@[simp] theorem Bool.not_false : (!false) = true := by decide
@[simp] theorem Bool.not_beq_true (b : Bool) : (!(b == true)) = (b == false) := by cases b <;> rfl
@[simp] theorem Bool.not_beq_false (b : Bool) : (!(b == false)) = (b == true) := by cases b <;> rfl
@[simp] theorem Bool.not_eq_true' (b : Bool) : ((!b) = true) = (b = false) := by cases b <;> simp
@[simp] theorem Bool.not_eq_false' (b : Bool) : ((!b) = false) = (b = true) := by cases b <;> simp

@[simp] theorem Bool.beq_to_eq (a b : Bool) :
  (a == b) = (a = b) := by cases a <;> cases b <;> decide
@[simp] theorem Bool.not_beq_to_not_eq (a b : Bool) :
  (!(a == b)) = ¬(a = b) := by cases a <;> cases b <;> decide

@[simp] theorem Bool.not_eq_true (b : Bool) : (¬(b = true)) = (b = false) := by cases b <;> decide
@[simp] theorem Bool.not_eq_false (b : Bool) : (¬(b = false)) = (b = true) := by cases b <;> decide

@[simp] theorem decide_eq_true_eq [Decidable p] : (decide p = true) = p := propext <| Iff.intro of_decide_eq_true decide_eq_true
@[simp] theorem decide_not [h : Decidable p] : decide (¬ p) = !decide p := by cases h <;> rfl
@[simp] theorem not_decide_eq_true [h : Decidable p] : ((!decide p) = true) = ¬ p := by cases h <;> simp [decide, *]

@[simp] theorem heq_eq_eq {α : Sort u} (a b : α) : HEq a b = (a = b) := propext <| Iff.intro eq_of_heq heq_of_eq

@[simp] theorem cond_true (a b : α) : cond true a b = a := rfl
@[simp] theorem cond_false (a b : α) : cond false a b = b := rfl

@[simp] theorem beq_self_eq_true [BEq α] [LawfulBEq α] (a : α) : (a == a) = true := LawfulBEq.rfl
@[simp] theorem beq_self_eq_true' [DecidableEq α] (a : α) : (a == a) = true := by simp [BEq.beq]

@[simp] theorem bne_self_eq_false [BEq α] [LawfulBEq α] (a : α) : (a != a) = false := by simp [bne]
@[simp] theorem bne_self_eq_false' [DecidableEq α] (a : α) : (a != a) = false := by simp [bne]

@[simp] theorem Nat.le_zero_eq (a : Nat) : (a ≤ 0) = (a = 0) :=
  propext ⟨fun h => Nat.le_antisymm h (Nat.zero_le ..), fun h => by simp [h]⟩

@[simp] theorem decide_False : decide False = false := rfl
@[simp] theorem decide_True : decide True = true := rfl

@[simp] theorem bne_iff_ne [BEq α] [LawfulBEq α] (a b : α) : a != b ↔ a ≠ b := by
  simp [bne]; rw [← beq_iff_eq a b]; simp [-beq_iff_eq]
