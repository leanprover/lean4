/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
public import Init.KernelVM
public import Init.Grind
import Init.Data.Array.Lemmas
import Init.Data.Int.OfNat

/-!
# Reasoning about `Lean.KernelVM` programs

A partial-correctness Hoare logic for `Lean.KernelVM.Stmt`. Since `Lean.KernelVM.run` only reports
success, the facts a program checks are established as postconditions of the statements that run.
-/

@[expose] public section

namespace Lean.KernelVM

theorem readD_writeD (a : Array UInt64) (i j : Nat) (v : UInt64) :
    readD (writeD a i v) j = if i = j then v else readD a j := by
  unfold readD writeD
  grind

/-- Partial correctness: if `s` succeeds when run from a state satisfying `P`, the result satisfies `Q`. -/
def Triple (inputs : List Nat) (P : State → Prop) (s : Stmt) (Q : State → Prop) : Prop :=
  ∀ fuel st st', P st → s.exec inputs fuel st = some st' → Q st'

theorem Triple.seq {inputs P R Q s t} (h₁ : Triple inputs P s R) (h₂ : Triple inputs R t Q) :
    Triple inputs P (.seq s t) Q := by
  intro fuel st st' hP h
  cases fuel with
  | zero => simp [Stmt.exec] at h
  | succ fuel =>
    simp only [Stmt.exec] at h
    split at h
    · exact h₂ _ _ _ (h₁ _ _ _ hP ‹_›) h
    · contradiction

theorem Triple.set {inputs Q r e} :
    Triple inputs (fun st => ∀ v, e.eval inputs st = some v → Q { st with regs := writeD st.regs r v })
      (.set r e) Q := by
  intro fuel st st' hP h
  cases fuel with
  | zero => simp [Stmt.exec] at h
  | succ fuel =>
    simp only [Stmt.exec] at h
    split at h
    · cases h; exact hP _ ‹_›
    · contradiction

theorem Triple.skip {inputs Q} : Triple inputs Q .skip Q := by
  intro fuel st st' hP h
  cases fuel with
  | zero => simp [Stmt.exec] at h
  | succ fuel => simp only [Stmt.exec, Option.some.injEq] at h; exact h ▸ hP

theorem Triple.store {inputs Q addr val} :
    Triple inputs (fun st => ∀ a v, addr.eval inputs st = some a → val.eval inputs st = some v →
      Q { st with mem := writeD st.mem a.toNat v }) (.store addr val) Q := by
  intro fuel st st' hP h
  cases fuel with
  | zero => simp [Stmt.exec] at h
  | succ fuel =>
    simp only [Stmt.exec] at h
    split at h
    · cases h; exact hP _ _ ‹_› ‹_›
    · contradiction

theorem Triple.ite {inputs P Q c t e}
    (ht : Triple inputs (fun st => P st ∧ ∃ v, c.eval inputs st = some v ∧ v ≠ 0) t Q)
    (he : Triple inputs (fun st => P st ∧ c.eval inputs st = some 0) e Q) :
    Triple inputs P (.ite c t e) Q := by
  intro fuel st st' hP h
  cases fuel with
  | zero => simp [Stmt.exec] at h
  | succ fuel =>
    simp only [Stmt.exec] at h
    split at h
    · rename_i v hv
      split at h
      · rename_i hne; exact ht _ _ _ ⟨hP, v, hv, by simpa using hne⟩ h
      · rename_i hz; exact he _ _ _ ⟨hP, by simp_all⟩ h
    · contradiction

theorem Triple.assert {inputs Q c} :
    Triple inputs (fun st => ∀ v, c.eval inputs st = some v → v ≠ 0 → Q st) (.assert c) Q := by
  intro fuel st st' hP h
  cases fuel with
  | zero => simp [Stmt.exec] at h
  | succ fuel =>
    simp only [Stmt.exec] at h
    split at h
    · split at h
      · rename_i hne; cases h; exact hP _ ‹_› (by simpa using hne)
      · contradiction
    · contradiction

theorem Triple.while {inputs c body Q} (I : State → Prop)
    (hbody : Triple inputs (fun st => I st ∧ ∃ v, c.eval inputs st = some v ∧ v ≠ 0) body I)
    (hexit : ∀ st, I st → c.eval inputs st = some 0 → Q st) :
    Triple inputs I (.while c body) Q := by
  intro fuel
  induction fuel with
  | zero => intro st st' _ h; simp [Stmt.exec] at h
  | succ fuel ih =>
    intro st st' hI h
    simp only [Stmt.exec] at h
    split at h
    · rename_i v hv
      split at h
      · rename_i hne
        split at h
        · exact ih _ _ (hbody _ _ _ ⟨hI, v, hv, by simpa using hne⟩ ‹_›) h
        · contradiction
      · cases h; exact hexit _ hI (by simp_all)
    · contradiction

theorem Triple.conseq {inputs P P' Q s} (h : Triple inputs P' s Q) (hP : ∀ st, P st → P' st) :
    Triple inputs P s Q :=
  fun fuel st st' hst hex => h fuel st st' (hP st hst) hex

theorem Triple.run {p : Prog} {inputs fuel Q} (h : Triple inputs (fun st => st = {}) p.body Q)
    (hrun : run p inputs fuel = true) : ∃ st, Q st := by
  unfold KernelVM.run at hrun
  match hex : p.body.exec inputs fuel {} with
  | some st => exact ⟨st, h _ _ _ rfl hex⟩
  | none => simp [hex] at hrun

@[simp] theorem ofBool_eq_zero (b : Bool) : ofBool b = 0 ↔ b = false := by cases b <;> decide

@[simp] theorem ofBool_ne_zero (b : Bool) : ofBool b ≠ 0 ↔ b = true := by cases b <;> decide

end Lean.KernelVM
