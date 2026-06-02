/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Rennie
-/
module

prelude
public import Std.Sat.AIG.Lemmas
import Init.Omega

@[expose] public section

/-!
This module contains functions to detect compound logic gates represented by sub-graphs of the `AIG`.
-/

namespace Std
namespace Sat

namespace AIG

variable {α : Type} [Hashable α] [DecidableEq α]

/--
Try to detect an XOR/XNOR gate rooted at the given entrypoint, returning a pair of `Refs` with
the same semantics as `entry` when XORed.

This can detect XOR/XNOR gates represented in the two-level form `¬(a ∧ b) ∧ ¬(¬a ∧ ¬b)` up to
permutation of inputs and negation of inputs and output.
-/
def detectXor (entry : Entrypoint α) : Option entry.aig.BinaryInput := do
  have := entry.ref.hgate
  -- Match root = (l ∧ r)
  let (eq:=hroot) .gate l r := entry.aig.decls[entry.ref.gate] | none
  have := entry.aig.hdag entry.ref.hgate hroot

  -- We expect the structure to be a (potentially inverted) conjunction of disjunctions so l/r
  -- must be inverted
  let true := l.invert && r.invert | none

  -- Match l = (l0 ∧ l1)
  let (eq:=hl) .gate l0 l1 := entry.aig.decls[l.gate] | none
  have := entry.aig.hdag (by omega) hl

  -- Match r = (r0 ∧ r1)
  let (eq:=hr) .gate r0 r1 := entry.aig.decls[r.gate] | none
  have := entry.aig.hdag (by omega) hr

  -- l and r must have the same inputs with opposite inversions to be an xor. We consider both
  -- permutations of l/r inputs with one another.
  if (l0 = r0.flip true ∧ l1 = r1.flip true) ∨ (l1 = r0.flip true ∧ l0 = r1.flip true) then
    -- If the root is uninverted, the gate represents `l0 xor l1`, otherwise it represents
    -- `l0 xnor l1` = `l0 xor ¬l1`.
    let lhs := ⟨l0.gate, l0.invert, by omega⟩
    let rhs := (⟨l1.gate, l1.invert, by omega⟩ : Ref entry.aig).flip entry.ref.invert
    some ⟨lhs, rhs⟩
  else
    none

variable {assign}

theorem denote_detectXor {entry : Entrypoint α} {fi : entry.aig.BinaryInput} (heq : detectXor entry = some fi) :
    ⟦entry, assign⟧ = (⟦entry.aig, fi.lhs, assign⟧ ^^ ⟦entry.aig, fi.rhs, assign⟧) := by
  simp only [detectXor] at heq
  split at heq; (all_goals try contradiction); next l r hroot =>
  split at heq; (all_goals try contradiction); next hinvert =>
  split at heq; (all_goals try contradiction); next l0 l1 hl =>
  split at heq; (all_goals try contradiction); next r0 r1 hr =>
  split at heq; (all_goals try contradiction); next hmatch =>
  · simp at hinvert
    rw [denote_idx_gate hroot, hinvert.left, hinvert.right, denote_idx_gate hl, denote_idx_gate hr]
    simp only [Option.some.injEq] at heq
    rcases hmatch with ⟨hl0, hl1⟩ | ⟨hl0, hl1⟩
    · have {a b : Bool} : ((a || b) && (!a || !b)) = (a ^^ b) := by cases a <;> cases b <;> decide
      simp only [hl0, Fanin.gate_flip, Fanin.invert_flip, Bool.bne_true, denote_not_invert, hl1,
        Bool.not_and, Bool.not_not, this, ← heq]
      <;> cases r0.invert
      <;> cases r1.invert
      <;> cases entry.ref.invert
      <;> simp
    · have {a b : Bool} : ((a || b) && (!b || !a)) = (a ^^ b) := by cases a <;> cases b <;> decide
      simp only [hl0, Fanin.gate_flip, Fanin.invert_flip, Bool.bne_true, denote_not_invert, hl1,
        Bool.not_and, Bool.not_not, this, ← heq]
      <;> cases r0.invert
      <;> cases r1.invert
      <;> cases entry.ref.invert
      <;> simp

theorem detectXor_lhs_lt {entry : Entrypoint α} {fi : entry.aig.BinaryInput} (heq : detectXor entry = some fi) :
    fi.lhs.gate < entry.ref.gate := by
  simp only [detectXor] at heq
  split at heq; (all_goals try contradiction); next l r hroot =>
  split at heq; (all_goals try contradiction); next hinvert =>
  split at heq; (all_goals try contradiction); next l0 l1 hl =>
  split at heq; (all_goals try contradiction); next r0 r1 hr =>
  split at heq; (all_goals try contradiction); next hmatch =>
  have := entry.ref.hgate
  have := entry.aig.hdag (by omega) hroot
  have := entry.aig.hdag (by omega) hl
  rw [Option.some.injEq] at heq
  simp only [← heq]
  omega

theorem detectXor_rhs_lt {entry : Entrypoint α} {fi : entry.aig.BinaryInput} (heq : detectXor entry = some fi) :
    fi.rhs.gate < entry.ref.gate := by
  simp only [detectXor] at heq
  split at heq; (all_goals try contradiction); next l r hroot =>
  split at heq; (all_goals try contradiction); next hinvert =>
  split at heq; (all_goals try contradiction); next l0 l1 hl =>
  split at heq; (all_goals try contradiction); next r0 r1 hr =>
  split at heq; (all_goals try contradiction); next hmatch =>
  have := entry.ref.hgate
  have := entry.aig.hdag (by omega) hroot
  have := entry.aig.hdag (by omega) hl
  rw [Option.some.injEq] at heq
  simp only [← heq, Ref.gate_flip]
  omega

end AIG

end Sat
end Std
