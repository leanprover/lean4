/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.AIG.LawfulOperator
import Init.Omega

@[expose] public section

/-!
This module provides a basic theory around the naive AIG node creation functions. It is mostly
fundamental work for the cached versions later on.
-/

namespace Std
namespace Sat

namespace AIG

variable {α : Type} [Hashable α] [DecidableEq α]

@[simp]
theorem Ref.gate_cast {aig1 aig2 : AIG α} (ref : Ref aig1)
    (h : aig1.decls.size ≤ aig2.decls.size) :
    (ref.cast h).gate = ref.gate := rfl

@[simp]
theorem Ref.cast_eq {aig1 aig2 : AIG α} (ref : Ref aig1)
    (h : aig1.decls.size ≤ aig2.decls.size) :
    (ref.cast h) = ⟨ref.gate, ref.invert, by have := ref.hgate; omega⟩ := rfl

@[simp]
theorem BinaryInput.lhs_cast {aig1 aig2 : AIG α} (input : BinaryInput aig1)
    (h : aig1.decls.size ≤ aig2.decls.size) :
    (input.cast h).lhs = input.lhs.cast h := rfl

@[simp]
theorem BinaryInput.rhs_cast {aig1 aig2 : AIG α} (input : BinaryInput aig1)
    (h : aig1.decls.size ≤ aig2.decls.size) :
    (input.cast h).rhs = input.rhs.cast h := rfl

@[simp]
theorem BinaryInput.each_cast {aig1 aig2 : AIG α} (lhs rhs : Ref aig1)
    (h1 h2 : aig1.decls.size ≤ aig2.decls.size) :
    BinaryInput.mk (lhs.cast h1) (rhs.cast h2) = (BinaryInput.mk lhs rhs).cast h2 := by
  simp [BinaryInput.cast]

@[simp]
theorem BinaryInput_invert_lhs {aig : AIG α} (input : BinaryInput aig) (linv rinv : Bool) :
    (input.invert linv rinv).lhs = ⟨input.lhs.gate, linv ^^ input.lhs.invert, input.lhs.hgate⟩ := by
  simp [BinaryInput.invert, Ref.flip]

@[simp]
theorem BinaryInput_invert_rhs {aig : AIG α} (input : BinaryInput aig) (linv rinv : Bool) :
    (input.invert linv rinv).rhs = ⟨input.rhs.gate, rinv ^^ input.rhs.invert, input.rhs.hgate⟩ := by
  simp [BinaryInput.invert, Ref.flip]

@[simp]
theorem denote_projected_entry {entry : Entrypoint α} :
    ⟦entry.aig, entry.ref, assign⟧ = ⟦entry, assign⟧ := by
  cases entry; simp

@[simp]
theorem denote_projected_entry' {entry : Entrypoint α} :
    ⟦entry.aig, ⟨entry.ref.gate, entry.ref.invert, entry.ref.hgate⟩, assign⟧ = ⟦entry, assign⟧ := by
  cases entry; simp

@[simp]
theorem Ref.denote_flip {aig : AIG α} {ref : Ref aig} {inv : Bool} :
    ⟦aig, ref.flip inv, assign⟧ = (⟦aig, ref, assign⟧ ^^ inv) := by
  unfold denote
  cases ref <;> cases inv <;> simp [Ref.flip]

@[simp]
theorem Ref.denote_not {aig : AIG α} {ref : Ref aig} :
    ⟦aig, ref.not, assign⟧ = !⟦aig, ref, assign⟧ := by
  simp [Ref.not]

@[simp]
theorem denote_not_invert {aig : AIG α} {gate} {inv} {hgate} :
    ⟦aig, ⟨gate, !inv, hgate⟩, assign⟧ = !⟦aig, ⟨gate, inv, hgate⟩, assign⟧ := by
  unfold denote
  simp

@[simp]
theorem denote_invert_true {aig : AIG α} {gate} {hgate} :
    ⟦aig, ⟨gate, true, hgate⟩, assign⟧ = !⟦aig, ⟨gate, false, hgate⟩, assign⟧ := by
  unfold denote
  simp

/--
If an index contains a `Decl.false` we know how to denote it.
-/
theorem denote_idx_false {aig : AIG α} {hstart} (h : aig.decls[start]'hstart = .false) :
    ⟦aig, ⟨start, invert, hstart⟩, assign⟧ = invert := by
  unfold denote denote.go
  split <;> simp_all

/--
If an index contains a `Decl.atom` we know how to denote it.
-/
theorem denote_idx_atom {aig : AIG α} {hstart} (h : aig.decls[start] = .atom a) :
    ⟦aig, ⟨start, invert, hstart⟩, assign⟧ = (assign a ^^ invert) := by
  unfold denote denote.go
  split <;> simp_all

/--
If an index contains a `Decl.gate` we know how to denote it.
-/
theorem denote_idx_gate {aig : AIG α} {hstart} (h : aig.decls[start] = .gate lhs rhs) :
    ⟦aig, ⟨start, invert, hstart⟩, assign⟧
      =
    ((
      (⟦aig, ⟨lhs.gate, lhs.invert, by have := aig.hdag hstart h; omega⟩, assign⟧)
        &&
      (⟦aig, ⟨rhs.gate, rhs.invert, by have := aig.hdag hstart h; omega⟩, assign⟧)
    ) ^^ invert) := by
  unfold denote
  conv =>
    lhs
    unfold denote.go
  split
  · simp_all
  · simp_all
  next heq =>
    rw [h] at heq
    simp_all

theorem idx_trichotomy (aig : AIG α) (hstart : start < aig.decls.size) {prop : Prop}
    (hfalse : aig.decls[start]'hstart = .false → prop)
    (hatom : ∀ a, aig.decls[start]'hstart = .atom a → prop)
    (hgate : ∀ lhs rhs , aig.decls[start]'hstart = .gate lhs rhs → prop)
    : prop := by
  match h : aig.decls[start]'hstart with
  | .false => apply hfalse; assumption
  | .atom a => apply hatom; assumption
  | .gate lhs rhs => apply hgate; assumption

theorem denote_idx_trichotomy {aig : AIG α} {hstart : start < aig.decls.size}
    (hfalse : aig.decls[start]'hstart = .false → ⟦aig, ⟨start, invert, hstart⟩, assign⟧ = res)
    (hatom : ∀ a, aig.decls[start]'hstart = .atom a → ⟦aig, ⟨start, invert, hstart⟩, assign⟧ = res)
    (hgate :
      ∀ lhs rhs,
        aig.decls[start]'hstart = .gate lhs rhs
          →
        ⟦aig, ⟨start, invert, hstart⟩, assign⟧ = res
    ) :
    ⟦aig, ⟨start, invert, hstart⟩, assign⟧ = res := by
  apply idx_trichotomy aig hstart
  · exact hfalse
  · exact hatom
  · exact hgate

theorem mem_def {aig : AIG α} {a : α} : (a ∈ aig) ↔ ((.atom a) ∈ aig.decls) := by
  simp [Membership.mem, Mem]

theorem denote_congr (assign1 assign2 : α → Bool) (aig : AIG α) (idx : Nat) (invert : Bool)
    (hidx : idx < aig.decls.size) (h : ∀ a, a ∈ aig → assign1 a = assign2 a) :
    ⟦aig, ⟨idx, invert, hidx⟩, assign1⟧ = ⟦aig, ⟨idx, invert, hidx⟩, assign2⟧ := by
  apply denote_idx_trichotomy
  · intro heq
    simp [denote_idx_false heq]
  · intro a heq
    simp only [denote_idx_atom heq, Bool.bne_left_inj]
    apply h
    simp [mem_def, ← heq]
  · intro lhs rhs heq
    simp only [denote_idx_gate heq]
    have := aig.hdag hidx heq
    rw [denote_congr assign1 assign2 aig lhs.gate _ (by omega) h]
    rw [denote_congr assign1 assign2 aig rhs.gate _ (by omega) h]

theorem of_isConstant {aig : AIG α} {assign : α → Bool} {ref : Ref aig} {b : Bool} :
    aig.isConstant ref b → ⟦aig, ref, assign⟧ = b := by
  rcases ref with ⟨gate, invert, hgate⟩
  intro h
  unfold isConstant at h
  dsimp only at h
  split at h
  next heq =>
    rw [denote_idx_false heq]
    cases invert <;> simp_all
  · contradiction

theorem denote_getConstant {aig : AIG α} {assign : α → Bool} {ref : Ref aig} {b : Bool} :
    aig.getConstant ref = some b → ⟦aig, ref, assign⟧ = b := by
  rcases ref with ⟨gate, invert, hgate⟩
  intro h
  unfold getConstant at h
  dsimp only at h
  split at h
  next heq =>
    rw [denote_idx_false heq]
    cases invert <;> simp_all
  · contradiction

end AIG

end Sat
end Std
