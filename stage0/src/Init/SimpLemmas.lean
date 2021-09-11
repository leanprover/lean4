/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

notation, basic datatypes and type classes
-/
prelude
import Init.Core

@[simp] theorem eq_self (a : α) : (a = a) = True :=
  propext <| Iff.intro (fun _ => trivial) (fun _ => rfl)

theorem of_eq_true (h : p = True) : p :=
  h ▸ trivial

theorem eq_true (h : p) : p = True :=
  propext <| Iff.intro (fun _ => trivial) (fun _ => h)

theorem eq_false (h : ¬ p) : p = False :=
  propext <| Iff.intro (fun h' => absurd h' h) (fun h' => False.elim h')

theorem eq_false' (h : p → False) : p = False :=
  propext <| Iff.intro (fun h' => absurd h' h) (fun h' => False.elim h')

theorem eq_true_of_decide {p : Prop} {s : Decidable p} (h : decide p = true) : p = True :=
  propext <| Iff.intro (fun h => trivial) (fun _ => of_decide_eq_true h)

theorem eq_false_of_decide {p : Prop} {s : Decidable p} (h : decide p = false) : p = False :=
  propext <| Iff.intro (fun h' => absurd h' (of_decide_eq_false h)) (fun h => False.elim h)

theorem implies_congr {p₁ p₂ : Sort u} {q₁ q₂ : Sort v} (h₁ : p₁ = p₂) (h₂ : q₁ = q₂) : (p₁ → q₁) = (p₂ → q₂) :=
  h₁ ▸ h₂ ▸ rfl

theorem implies_congr_ctx {p₁ p₂ q₁ q₂ : Prop} (h₁ : p₁ = p₂) (h₂ : p₂ → q₁ = q₂) : (p₁ → q₁) = (p₂ → q₂) :=
  propext <| Iff.intro
    (fun h hp₂ =>
      have : p₁ := h₁ ▸ hp₂
      have : q₁ := h this
      h₂ hp₂ ▸ this)
    (fun h hp₁ =>
      have hp₂ : p₂ := h₁ ▸ hp₁
      have : q₂ := h hp₂
      h₂ hp₂ ▸ this)

theorem forall_congr {α : Sort u} {p q : α → Prop} (h : ∀ a, (p a = q a)) : (∀ a, p a) = (∀ a, q a) :=
  have : p = q := funext h
  this ▸ rfl

theorem let_congr {α : Sort u} {β : Sort v} {a a' : α} {b b' : α → β} (h₁ : a = a') (h₂ : ∀ x, b x = b' x) :
        (let x := a; b x) = (let x := a'; b' x) := by
  subst h₁
  have : b = b' := funext h₂
  subst this
  rfl

theorem let_val_congr {α : Sort u} {β : Sort v} {a a' : α} (b : α → β) (h : a = a') :
        (let x := a; b x) = (let x := a'; b x) := by
  subst h
  rfl

theorem let_body_congr {α : Sort u} {β : α → Sort v} {b b' : (a : α) → β a} (a : α) (h : ∀ x, b x = b' x) :
        (let x := a; b x) = (let x := a; b' x) := by
  have : b = b' := funext h
  subst this
  rfl

@[congr]
theorem ite_congr {x y u v : α} {s : Decidable b} [Decidable c] (h₁ : b = c) (h₂ : c → x = u) (h₃ : ¬ c → y = v) : ite b x y = ite c u v := by
  cases Decidable.em c with
  | inl h => rw [if_pos h]; subst b; rw[if_pos h]; exact h₂ h
  | inr h => rw [if_neg h]; subst b; rw[if_neg h]; exact h₃ h

theorem Eq.mpr_prop {p q : Prop} (h₁ : p = q) (h₂ : q) : p :=
  h₁ ▸ h₂

theorem Eq.mpr_not {p q : Prop} (h₁ : p = q) (h₂ : ¬q) : ¬p :=
  h₁ ▸ h₂

@[congr]
theorem dite_congr {s : Decidable b} [Decidable c]
        {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
        (h₁ : b = c)
        (h₂ : (h : c)  → x (Eq.mpr_prop h₁ h) = u h)
        (h₃ : (h : ¬c) → y (Eq.mpr_not h₁ h)  = v h)
        : dite b x y = dite c u v := by
  cases Decidable.em c with
  | inl h => rw [dif_pos h]; subst b; rw [dif_pos h]; exact h₂ h
  | inr h => rw [dif_neg h]; subst b; rw [dif_neg h]; exact h₃ h

@[simp] theorem ne_eq (a b : α) : (a ≠ b) = Not (a = b) := rfl
@[simp] theorem ite_true (a b : α) : (if True then a else b) = a := rfl
@[simp] theorem ite_false (a b : α) : (if False then a else b) = b := rfl
@[simp] theorem dite_true {α : Sort u} {t : True → α} {e : ¬ True → α} : (dite True t e) = t True.intro := rfl
@[simp] theorem dite_false {α : Sort u} {t : False → α} {e : ¬ False → α} : (dite False t e) = e not_false := rfl
@[simp] theorem and_self (p : Prop) : (p ∧ p) = p := propext <| Iff.intro (fun h => h.1) (fun h => ⟨h, h⟩)
@[simp] theorem and_true (p : Prop) : (p ∧ True) = p := propext <| Iff.intro (fun h => h.1) (fun h => ⟨h, trivial⟩)
@[simp] theorem true_and (p : Prop) : (True ∧ p) = p := propext <| Iff.intro (fun h => h.2) (fun h => ⟨trivial, h⟩)
@[simp] theorem and_false (p : Prop) : (p ∧ False) = False := propext <| Iff.intro (fun h => h.2) (fun h => False.elim h)
@[simp] theorem false_and (p : Prop) : (False ∧ p) = False := propext <| Iff.intro (fun h => h.1) (fun h => False.elim h)
@[simp] theorem or_self (p : Prop) : (p ∨ p) = p := propext <| Iff.intro (fun | Or.inl h => h | Or.inr h => h) (fun h => Or.inl h)
@[simp] theorem or_true (p : Prop) : (p ∨ True) = True := propext <| Iff.intro (fun h => trivial) (fun h => Or.inr trivial)
@[simp] theorem true_or (p : Prop) : (True ∨ p) = True := propext <| Iff.intro (fun h => trivial) (fun h => Or.inl trivial)
@[simp] theorem or_false (p : Prop) : (p ∨ False) = p := propext <| Iff.intro (fun | Or.inl h => h | Or.inr h => False.elim h) (fun h => Or.inl h)
@[simp] theorem false_or (p : Prop) : (False ∨ p) = p := propext <| Iff.intro (fun | Or.inr h => h | Or.inl h => False.elim h) (fun h => Or.inr h)
@[simp] theorem iff_self (p : Prop) : (p ↔ p) = True := propext <| Iff.intro (fun h => trivial) (fun _ => Iff.intro id id)
@[simp] theorem iff_true (p : Prop) : (p ↔ True) = p := propext <| Iff.intro (fun h => h.mpr trivial) (fun h => Iff.intro (fun _ => trivial) (fun _ => h))
@[simp] theorem true_iff (p : Prop) : (True ↔ p) = p := propext <| Iff.intro (fun h => h.mp trivial) (fun h => Iff.intro (fun _ => h) (fun _ => trivial))
@[simp] theorem iff_false (p : Prop) : (p ↔ False) = ¬p := propext <| Iff.intro (fun h hp => h.mp hp) (fun h => Iff.intro h False.elim)
@[simp] theorem false_iff (p : Prop) : (False ↔ p) = ¬p := propext <| Iff.intro (fun h hp => h.mpr hp) (fun h => Iff.intro False.elim h)
@[simp] theorem false_implies (p : Prop) : (False → p) = True := propext <| Iff.intro (fun _ => trivial) (by intros; trivial)
@[simp] theorem implies_true (p : Prop) : (p → True) = True := propext <| Iff.intro (fun _ => trivial) (by intros; trivial)
@[simp] theorem true_implies (p : Prop) : (True → p) = p := propext <| Iff.intro (fun h => h trivial) (by intros; trivial)

@[simp] theorem Bool.or_false (b : Bool) : (b || false) = b  := by cases b <;> rfl
@[simp] theorem Bool.or_true (b : Bool) : (b || true) = true := by cases b <;> rfl
@[simp] theorem Bool.false_or (b : Bool) : (false || b) = b  := by cases b <;> rfl
@[simp] theorem Bool.true_or (b : Bool) : (true || b) = true := by cases b <;> rfl
@[simp] theorem Bool.or_self (b : Bool) : (b || b) = b       := by cases b <;> rfl

@[simp] theorem Bool.and_false (b : Bool) : (b && false) = false := by cases b <;> rfl
@[simp] theorem Bool.and_true (b : Bool) : (b && true) = b       := by cases b <;> rfl
@[simp] theorem Bool.false_and (b : Bool) : (false && b) = false := by cases b <;> rfl
@[simp] theorem Bool.true_and (b : Bool) : (true && b) = b       := by cases b <;> rfl
@[simp] theorem Bool.and_self (b : Bool) : (b && b) = b          := by cases b <;> rfl
