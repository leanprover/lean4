/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Data.Rat.Basic
public import Init.Data.SInt.Basic
public import Init.Data.Int.DivMod.Lemmas
public import Init.Data.Nat.Dvd
public import Init.Data.String.Lemmas.StringOrder
import Init.Data.BitVec.Lemmas
import Init.Data.Int.Order
import Init.Data.UInt.Lemmas
import Init.ByCases
public section
namespace Lean.Sym

theorem not_true_eq : (¬ True) = False := by simp
theorem not_false_eq : (¬ False) = True := by simp

theorem or_eq_true_left (a b : Prop) (h : a = True) : (a ∨ b) = True := by simp [h]
theorem or_eq_right (a b : Prop) (h : a = False) : (a ∨ b) = b := by simp [h]

theorem and_eq_false_left (a b : Prop) (h : a = False) : (a ∧ b) = False := by simp [h]
theorem and_eq_left (a b : Prop) (h : a = True) : (a ∧ b) = b := by simp [h]

theorem imp_subst {α : Sort u} {x t : α} (motive : α → Prop) (k : x = t → motive t) :
    x = t → motive x :=
  fun h => Eq.substr (p := motive) h (k h)

theorem ite_cond_congr {α : Sort u} (c : Prop) {inst : Decidable c} (a b : α)
    (c' : Prop) {inst' : Decidable c'} (h : c = c') : @ite α c inst a b = @ite α c' inst' a b := by
  simp [*]

theorem ite_true {α : Sort u} (c : Prop) {inst : Decidable c} (a b : α) {ht : c} : @ite α c inst a b = a := by
  simp [*]

theorem ite_true_congr {α : Sort u} (c : Prop) {inst : Decidable c} (a b : α) (c' : Prop) (h : c = c') {ht : c'} : @ite α c inst a b = a := by
  simp [*]

theorem ite_false {α : Sort u} (c : Prop) {inst : Decidable c} (a b : α) {ht : ¬ c} : @ite α c inst a b = b := by
  simp [*]

theorem ite_false_congr {α : Sort u} (c : Prop) {inst : Decidable c} (a b : α) (c' : Prop) (h : c = c') {ht : ¬ c'} : @ite α c inst a b = b := by
  simp [*]

theorem ite_of_decide_eq_true {α : Sort u} (c : Prop) {inst : Decidable c} (a b : α) {ht : decide c = true} : @ite α c inst a b = a := by
  simp_all

theorem ite_of_decide_eq_false {α : Sort u} (c : Prop) {inst : Decidable c} (a b : α) {ht : decide c = false} : @ite α c inst a b = b := by
  simp_all

theorem ite_of_decide_eq_true_congr {α : Sort u} (c : Prop) {inst : Decidable c} (a b : α) (c' : Prop) (h : c = c') {_ : Decidable c'} {ht : decide c' = true} : @ite α c inst a b = a := by
  simp_all

theorem ite_of_decide_eq_false_congr {α : Sort u} (c : Prop) {inst : Decidable c} (a b : α) (c' : Prop) (h : c = c') {_ : Decidable c'} {ht : decide c' = false} : @ite α c inst a b = b := by
  simp_all

theorem dite_true {α : Sort u} (c : Prop) {inst : Decidable c} (a : c → α) (b : ¬ c → α) {ht : c} : @dite α c inst a b = a ht := by
  simp [*]

theorem dite_true_congr {α : Sort u} (c : Prop) {inst : Decidable c} (a : c → α) (b : ¬ c → α) (c' : Prop) (h : c = c') {ht : c'} : @dite α c inst a b = a (h.mpr_prop ht) := by
  subst h; simp [*]

theorem dite_false {α : Sort u} (c : Prop) {inst : Decidable c} (a : c → α) (b : ¬ c → α) {ht : ¬ c} : @dite α c inst a b = b ht := by
  simp [*]

theorem dite_false_congr {α : Sort u} (c : Prop) {inst : Decidable c} (a : c → α) (b : ¬ c → α) (c' : Prop) (h : c = c') {ht : ¬ c'} : @dite α c inst a b = b (h.mpr_not ht) := by
  subst h; simp [*]

theorem dite_cond_congr {α : Sort u} (c : Prop) {inst : Decidable c} (a : c → α) (b : ¬ c → α)
    (c' : Prop) {inst' : Decidable c'} (h : c = c')
    : @dite α c inst a b = @dite α c' inst' (fun h' => a (h.mpr_prop h')) (fun h' => b (h.mpr_not h')) := by
  simp [*]

theorem cond_cond_eq_true {α : Sort u} (c : Bool) (a b : α) (h : c = true) : cond c a b = a := by
  simp [*]

theorem cond_cond_eq_false {α : Sort u} (c : Bool) (a b : α) (h : c = false) : cond c a b = b := by
  simp [*]

theorem cond_cond_congr {α : Sort u} (c : Bool) (a b : α) (c' : Bool) (h : c = c') : cond c a b = cond c' a b := by
  simp [*]

theorem Nat.lt_eq_true (a b : Nat) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Int.lt_eq_true (a b : Int) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Rat.lt_eq_true (a b : Rat) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Int8.lt_eq_true (a b : Int8) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Int16.lt_eq_true (a b : Int16) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Int32.lt_eq_true (a b : Int32) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Int64.lt_eq_true (a b : Int64) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem UInt8.lt_eq_true (a b : UInt8) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem UInt16.lt_eq_true (a b : UInt16) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem UInt32.lt_eq_true (a b : UInt32) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem UInt64.lt_eq_true (a b : UInt64) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Fin.lt_eq_true (a b : Fin n) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem BitVec.lt_eq_true (a b : BitVec n) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem String.lt_eq_true (a b : String) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Char.lt_eq_true (a b : Char) (h : decide (a < b) = true) : (a < b) = True := by simp_all

theorem Nat.lt_eq_false (a b : Nat) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Int.lt_eq_false (a b : Int) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Rat.lt_eq_false (a b : Rat) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Int8.lt_eq_false (a b : Int8) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Int16.lt_eq_false (a b : Int16) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Int32.lt_eq_false (a b : Int32) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Int64.lt_eq_false (a b : Int64) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem UInt8.lt_eq_false (a b : UInt8) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem UInt16.lt_eq_false (a b : UInt16) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem UInt32.lt_eq_false (a b : UInt32) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem UInt64.lt_eq_false (a b : UInt64) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Fin.lt_eq_false (a b : Fin n) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem BitVec.lt_eq_false (a b : BitVec n) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem String.lt_eq_false (a b : String) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Char.lt_eq_false (a b : Char) (h : decide (a < b) = false) : (a < b) = False := by simp_all

theorem Nat.le_eq_true (a b : Nat) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Int.le_eq_true (a b : Int) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Rat.le_eq_true (a b : Rat) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Int8.le_eq_true (a b : Int8) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Int16.le_eq_true (a b : Int16) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Int32.le_eq_true (a b : Int32) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Int64.le_eq_true (a b : Int64) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem UInt8.le_eq_true (a b : UInt8) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem UInt16.le_eq_true (a b : UInt16) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem UInt32.le_eq_true (a b : UInt32) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem UInt64.le_eq_true (a b : UInt64) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Fin.le_eq_true (a b : Fin n) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem BitVec.le_eq_true (a b : BitVec n) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem String.le_eq_true (a b : String) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Char.le_eq_true (a b : Char) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all

theorem Nat.le_eq_false (a b : Nat) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Int.le_eq_false (a b : Int) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Rat.le_eq_false (a b : Rat) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Int8.le_eq_false (a b : Int8) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Int16.le_eq_false (a b : Int16) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Int32.le_eq_false (a b : Int32) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Int64.le_eq_false (a b : Int64) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem UInt8.le_eq_false (a b : UInt8) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem UInt16.le_eq_false (a b : UInt16) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem UInt32.le_eq_false (a b : UInt32) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem UInt64.le_eq_false (a b : UInt64) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Fin.le_eq_false (a b : Fin n) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem BitVec.le_eq_false (a b : BitVec n) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem String.le_eq_false (a b : String) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Char.le_eq_false (a b : Char) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all

theorem Bool.eq_eq_true (a b : Bool) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Nat.eq_eq_true (a b : Nat) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Int.eq_eq_true (a b : Int) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Rat.eq_eq_true (a b : Rat) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Int8.eq_eq_true (a b : Int8) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Int16.eq_eq_true (a b : Int16) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Int32.eq_eq_true (a b : Int32) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Int64.eq_eq_true (a b : Int64) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem UInt8.eq_eq_true (a b : UInt8) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem UInt16.eq_eq_true (a b : UInt16) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem UInt32.eq_eq_true (a b : UInt32) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem UInt64.eq_eq_true (a b : UInt64) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Fin.eq_eq_true (a b : Fin n) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem BitVec.eq_eq_true (a b : BitVec n) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Char.eq_eq_true (a b : Char) (h : decide (a = b) = true) : (a = b) = True := by simp_all

theorem Bool.eq_eq_false (a b : Bool) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Nat.eq_eq_false (a b : Nat) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Int.eq_eq_false (a b : Int) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Rat.eq_eq_false (a b : Rat) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Int8.eq_eq_false (a b : Int8) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Int16.eq_eq_false (a b : Int16) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Int32.eq_eq_false (a b : Int32) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Int64.eq_eq_false (a b : Int64) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem UInt8.eq_eq_false (a b : UInt8) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem UInt16.eq_eq_false (a b : UInt16) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem UInt32.eq_eq_false (a b : UInt32) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem UInt64.eq_eq_false (a b : UInt64) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Fin.eq_eq_false (a b : Fin n) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem BitVec.eq_eq_false (a b : BitVec n) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Char.eq_eq_false (a b : Char) (h : decide (a = b) = false) : (a = b) = False := by simp_all

theorem Nat.dvd_eq_true (a b : Nat) (h : decide (a ∣ b) = true) : (a ∣ b) = True := by simp_all
theorem Int.dvd_eq_true (a b : Int) (h : decide (a ∣ b) = true) : (a ∣ b) = True := by simp_all

theorem Nat.dvd_eq_false (a b : Nat) (h : decide (a ∣ b) = false) : (a ∣ b) = False := by simp_all
theorem Int.dvd_eq_false (a b : Int) (h : decide (a ∣ b) = false) : (a ∣ b) = False := by simp_all

theorem decide_isTrue (p : Prop) {inst : Decidable p} {h : p} : decide p = true := by simp [*]
theorem decide_isTrue_congr (p p' : Prop) (heq : p = p') {inst : Decidable p} {hp : p'} : decide p = true := by simp [*]

theorem decide_isFalse (p : Prop) {inst : Decidable p} {h : ¬p} : decide p = false := by simp [*]
theorem decide_isFalse_congr (p p' : Prop) (heq : p = p') {inst : Decidable p} {hnp : ¬p'} : decide p = false := by simp [*]

theorem decide_eq_congr (p p' : Prop) (heq : p = p') {inst : Decidable p} {inst' : Decidable p'}
    {b : Bool} {h : inst'.decide = b} : inst.decide = b := by
  subst heq; cases Subsingleton.allEq inst inst'; assumption

theorem decide_prop_eq_true (p : Prop) {inst : Decidable p} (h : p = True) : decide p = true := by simp [*]
theorem decide_prop_eq_false (p : Prop) {inst : Decidable p} (h : p = False) : decide p = false := by simp [*]

theorem eq_prop_eq_and (p q : Prop) : (p = q) = ((p → q) ∧ (q → p)) := by
  by_cases p <;> by_cases q <;> simp [*]
theorem iff_eq_and (p q : Prop) : (p ↔ q) = ((p → q) ∧ (q → p)) := by
  by_cases p <;> by_cases q <;> simp [*]
theorem ite_eq_and (c : Prop) [Decidable c] (t e : Prop) :
    (if c then t else e) = ((c → t) ∧ (¬c → e)) := by
  by_cases c <;> simp[*]
theorem cond_eq_and (c : Bool) (t e : Prop) :
    (bif c then t else e) = ((c → t) ∧ (¬c → e)) := by
  by_cases c <;> simp[*]
theorem imp_eq (p q : Prop) : (p → q) = (¬p ∨ q) := by
  by_cases p <;> simp[*]

theorem exists_and_eq (p : α → Prop) (q : Prop) : ((∃ x, p x) ∧ q) = (∃ x, p x ∧ q) := by
  simp

theorem and_exists_eq (p : Prop) (q : α → Prop) : (p ∧ ∃ x, q x) = (∃ x, p ∧ q x) := by
  simp

theorem exists_or_exists_eq (p q : α → Prop) : ((∃ x, p x) ∨ (∃ x, q x)) = (∃ x, p x ∨ q x) := by
  apply propext
  constructor
  · rintro (⟨x, hx⟩ | ⟨y, hy⟩)
    · exists x
      simp [hx]
    · exists y
      simp [hy]
  · rintro ⟨x, hx1 | hx2⟩
    · left
      exists x
    · right
      exists x

theorem forall_and_forall_eq (p q : α → Prop) : ((∀ x, p x) ∧ (∀ x, q x)) = (∀ x, p x ∧ q x) := by
  apply propext
  constructor
  · rintro ⟨h1, h2⟩ x
    exact ⟨h1 x, h2 x⟩
  · intro h
    constructor
    · exact fun x => (h x).left
    · exact fun x => (h x).right

theorem forall_or_eq (p : α → Prop) (q : Prop) : ((∀ x, p x) ∨ q) = (∀ x, p x ∨ q) := by
  apply propext
  constructor
  · rintro (h1 | h1) x
    · left
      exact h1 x
    · right
      exact h1
  · intro h1
    apply Classical.byContradiction
    simp only [not_or, Classical.not_forall, imp_false, not_and, Classical.not_not,
      forall_exists_index]
    intro x hx
    rcases h1 x with h2 | h2
    · contradiction
    · exact h2

theorem or_forall_eq (p : Prop) (q : α → Prop) : (p ∨ ∀ x, q x) = (∀ x, p ∨ q x) := by
  apply propext
  constructor
  · rintro (h1 | h1) x
    · left
      exact h1
    · right
      exact h1 x
  · intro h1
    apply Classical.byContradiction
    simp only [not_or, Classical.not_forall, imp_false, not_and, not_exists, Classical.not_not]
    intro hp x
    rcases h1 x with h2 | h2
    · contradiction
    · exact h2

theorem forall_and_eq [Nonempty α] (p : α → Prop) (q : Prop) : ((∀ x, p x) ∧ q) = (∀ x, p x ∧ q) := by
  apply propext
  constructor
  · rintro ⟨h, hq⟩ x
    exact ⟨h x, hq⟩
  · intro h
    obtain ⟨x⟩ := ‹Nonempty α›
    exact ⟨fun x => (h x).1, (h x).2⟩

theorem and_forall_eq [Nonempty α] (p : Prop) (q : α → Prop) : (p ∧ ∀ x, q x) = (∀ x, p ∧ q x) := by
  apply propext
  constructor
  · rintro ⟨hp, h⟩ x
    exact ⟨hp, h x⟩
  · intro h
    obtain ⟨x⟩ := ‹Nonempty α›
    exact ⟨(h x).1, fun x => (h x).2⟩

theorem exists_or_eq [Nonempty α] (p : α → Prop) (q : Prop) : ((∃ x, p x) ∨ q) = (∃ x, p x ∨ q) := by
  apply propext
  constructor
  · rintro (⟨x, hx⟩ | hq)
    · exact ⟨x, .inl hx⟩
    · obtain ⟨x⟩ := ‹Nonempty α›
      exact ⟨x, .inr hq⟩
  · rintro ⟨x, hx | hq⟩
    · exact .inl ⟨x, hx⟩
    · exact .inr hq

theorem or_exists_eq [Nonempty α] (p : Prop) (q : α → Prop) : (p ∨ ∃ x, q x) = (∃ x, p ∨ q x) := by
  apply propext
  constructor
  · rintro (hp | ⟨x, hx⟩)
    · obtain ⟨x⟩ := ‹Nonempty α›
      exact ⟨x, .inl hp⟩
    · exact ⟨x, .inr hx⟩
  · rintro ⟨x, hp | hx⟩
    · exact .inl hp
    · exact .inr ⟨x, hx⟩

end Lean.Sym
