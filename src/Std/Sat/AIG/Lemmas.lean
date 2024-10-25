/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.Basic
import Std.Sat.AIG.LawfulOperator

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
    (ref.cast h) = ⟨ref.gate, by have := ref.hgate; omega⟩ := rfl

@[simp]
theorem Fanin.ref_cast {aig1 aig2 : AIG α} (fanin : Fanin aig1)
    (h : aig1.decls.size ≤ aig2.decls.size) :
    (fanin.cast h).ref = fanin.ref.cast h := rfl

@[simp]
theorem Fanin.inv_cast {aig1 aig2 : AIG α} (fanin : Fanin aig1)
    (h : aig1.decls.size ≤ aig2.decls.size) :
    (fanin.cast h).inv = fanin.inv := rfl

@[simp]
theorem GateInput.lhs_cast {aig1 aig2 : AIG α} (input : GateInput aig1)
    (h : aig1.decls.size ≤ aig2.decls.size) :
    (input.cast h).lhs = input.lhs.cast h := rfl

@[simp]
theorem GateInput.rhs_cast {aig1 aig2 : AIG α} (input : GateInput aig1)
    (h : aig1.decls.size ≤ aig2.decls.size) :
    (input.cast h).rhs = input.rhs.cast h := rfl

@[simp]
theorem BinaryInput.each_cast {aig1 aig2 : AIG α} (lhs rhs : Ref aig1)
    (h1 h2 : aig1.decls.size ≤ aig2.decls.size) :
    BinaryInput.mk (lhs.cast h1) (rhs.cast h2) = (BinaryInput.mk lhs rhs).cast h2 := by
  simp [BinaryInput.cast]

@[simp]
theorem denote_projected_entry {entry : Entrypoint α} :
    ⟦entry.aig, entry.ref, assign⟧ = ⟦entry, assign⟧ := by
  cases entry; simp

@[simp]
theorem denote_projected_entry' {entry : Entrypoint α} :
    ⟦entry.aig, ⟨entry.ref.gate, entry.ref.hgate⟩, assign⟧ = ⟦entry, assign⟧ := by
  cases entry; simp

/--
`AIG.mkGate` never shrinks the underlying AIG.
-/
theorem mkGate_le_size (aig : AIG α) (input : GateInput aig) :
    aig.decls.size ≤ (aig.mkGate input).aig.decls.size := by
  simp_arith [mkGate]

/--
The AIG produced by `AIG.mkGate` agrees with the input AIG on all indices that are valid for both.
-/
theorem mkGate_decl_eq idx (aig : AIG α) (input : GateInput aig) {h : idx < aig.decls.size} :
    have := mkGate_le_size aig input
    (aig.mkGate input).aig.decls[idx]'(by omega) = aig.decls[idx] := by
  simp only [mkGate, Array.getElem_push]
  split
  · rfl
  · contradiction

instance : LawfulOperator α GateInput mkGate where
  le_size := mkGate_le_size
  decl_eq := by
    intros
    apply mkGate_decl_eq

@[simp]
theorem denote_mkGate {aig : AIG α} {input : GateInput aig} :
    ⟦aig.mkGate input, assign⟧
      =
    ((⟦aig, input.lhs.ref, assign⟧ ^^ input.lhs.inv) && (⟦aig, input.rhs.ref, assign⟧ ^^ input.rhs.inv)) := by
  conv =>
    lhs
    unfold denote denote.go
  split
  · next heq =>
    rw [mkGate, Array.getElem_push_eq] at heq
    contradiction
  · next heq =>
    rw [mkGate, Array.getElem_push_eq] at heq
    contradiction
  · next heq =>
    rw [mkGate, Array.getElem_push_eq] at heq
    injection heq with heq1 heq2 heq3 heq4
    dsimp only
    congr 2
    · unfold denote
      simp only [heq1]
      apply denote.go_eq_of_isPrefix
      apply LawfulOperator.isPrefix_aig
    · simp [heq3]
    · unfold denote
      simp only [heq2]
      apply denote.go_eq_of_isPrefix
      apply LawfulOperator.isPrefix_aig
    · simp [heq4]

/--
`AIG.mkAtom` never shrinks the underlying AIG.
-/
theorem mkAtom_le_size (aig : AIG α) (var : α) :
    aig.decls.size ≤ (aig.mkAtom var).aig.decls.size := by
  simp_arith [mkAtom]

/--
The AIG produced by `AIG.mkAtom` agrees with the input AIG on all indices that are valid for both.
-/
theorem mkAtom_decl_eq (aig : AIG α) (var : α) (idx : Nat) {h : idx < aig.decls.size} {hbound} :
    (aig.mkAtom var).aig.decls[idx]'hbound = aig.decls[idx] := by
  simp only [mkAtom, Array.getElem_push]
  split
  · rfl
  · contradiction

instance : LawfulOperator α (fun _ => α) mkAtom where
  le_size := mkAtom_le_size
  decl_eq := by
    intros
    apply mkAtom_decl_eq

@[simp]
theorem denote_mkAtom {aig : AIG α} :
    ⟦(aig.mkAtom var), assign⟧ = assign var := by
  unfold denote denote.go
  split
  · next heq =>
    rw [mkAtom, Array.getElem_push_eq] at heq
    contradiction
  · next heq =>
    rw [mkAtom, Array.getElem_push_eq] at heq
    injection heq with heq
    rw [heq]
  · next heq =>
    rw [mkAtom, Array.getElem_push_eq] at heq
    contradiction

/--
`AIG.mkConst` never shrinks the underlying AIG.
-/
theorem mkConst_le_size (aig : AIG α) (val : Bool) :
    aig.decls.size ≤ (aig.mkConst val).aig.decls.size := by
  simp_arith [mkConst]

/--
The AIG produced by `AIG.mkConst` agrees with the input AIG on all indices that are valid for both.
-/
theorem mkConst_decl_eq (aig : AIG α) (val : Bool) (idx : Nat) {h : idx < aig.decls.size} :
    have := mkConst_le_size aig val
    (aig.mkConst val).aig.decls[idx]'(by omega) = aig.decls[idx] := by
  simp only [mkConst, Array.getElem_push]
  split
  · rfl
  · contradiction

instance : LawfulOperator α (fun _ => Bool) mkConst where
  le_size := mkConst_le_size
  decl_eq := by
    intros
    apply mkConst_decl_eq

@[simp]
theorem denote_mkConst {aig : AIG α} : ⟦(aig.mkConst val), assign⟧ = val := by
  unfold denote denote.go
  split
  · next heq =>
    rw [mkConst, Array.getElem_push_eq] at heq
    injection heq with heq
    rw [heq]
  · next heq =>
    rw [mkConst, Array.getElem_push_eq] at heq
    contradiction
  · next heq =>
    rw [mkConst, Array.getElem_push_eq] at heq
    contradiction

/--
If an index contains a `Decl.const` we know how to denote it.
-/
theorem denote_idx_const {aig : AIG α} {hstart} (h : aig.decls[start]'hstart = .const b) :
    ⟦aig, ⟨start, hstart⟩, assign⟧ = b := by
  unfold denote denote.go
  split <;> simp_all

/--
If an index contains a `Decl.atom` we know how to denote it.
-/
theorem denote_idx_atom {aig : AIG α} {hstart} (h : aig.decls[start] = .atom a) :
    ⟦aig, ⟨start, hstart⟩, assign⟧ = assign a := by
  unfold denote denote.go
  split <;> simp_all

/--
If an index contains a `Decl.gate` we know how to denote it.
-/
theorem denote_idx_gate {aig : AIG α} {hstart} (h : aig.decls[start] = .gate lhs rhs linv rinv) :
    ⟦aig, ⟨start, hstart⟩, assign⟧
      =
    (
      (⟦aig, ⟨lhs, by have := aig.invariant hstart h; omega⟩, assign⟧ ^^ linv)
        &&
      (⟦aig, ⟨rhs, by have := aig.invariant hstart h; omega⟩, assign⟧ ^^ rinv)
    ) := by
  unfold denote
  conv =>
    lhs
    unfold denote.go
  split
  · simp_all
  · simp_all
  · next heq =>
    rw [h] at heq
    simp_all

theorem idx_trichotomy (aig : AIG α) (hstart : start < aig.decls.size) {prop : Prop}
    (hconst : ∀ b, aig.decls[start]'hstart = .const b → prop)
    (hatom : ∀ a, aig.decls[start]'hstart = .atom a → prop)
    (hgate : ∀ lhs rhs linv rinv, aig.decls[start]'hstart = .gate lhs rhs linv rinv → prop)
    : prop := by
  match h : aig.decls[start]'hstart with
  | .const b => apply hconst; assumption
  | .atom a => apply hatom; assumption
  | .gate lhs rhs linv rinv => apply hgate; assumption

theorem denote_idx_trichotomy {aig : AIG α} {hstart : start < aig.decls.size}
    (hconst : ∀ b, aig.decls[start]'hstart = .const b → ⟦aig, ⟨start, hstart⟩, assign⟧ = res)
    (hatom : ∀ a, aig.decls[start]'hstart = .atom a → ⟦aig, ⟨start, hstart⟩, assign⟧ = res)
    (hgate :
      ∀ lhs rhs linv rinv,
        aig.decls[start]'hstart = .gate lhs rhs linv rinv
          →
        ⟦aig, ⟨start, hstart⟩, assign⟧ = res
    ) :
    ⟦aig, ⟨start, hstart⟩, assign⟧ = res := by
  apply idx_trichotomy aig hstart
  · exact hconst
  · exact hatom
  · exact hgate

theorem mem_def {aig : AIG α} {a : α} : (a ∈ aig) ↔ ((.atom a) ∈ aig.decls) := by
  simp [Membership.mem, Mem]

theorem denote_congr (assign1 assign2 : α → Bool) (aig : AIG α) (idx : Nat)
    (hidx : idx < aig.decls.size) (h : ∀ a, a ∈ aig → assign1 a = assign2 a) :
    ⟦aig, ⟨idx, hidx⟩, assign1⟧ = ⟦aig, ⟨idx, hidx⟩, assign2⟧ := by
  apply denote_idx_trichotomy
  · intro b heq
    simp [denote_idx_const heq]
  · intro a heq
    simp only [denote_idx_atom heq]
    apply h
    rw [mem_def, ← heq, Array.mem_def]
    apply Array.getElem_mem_toList
  · intro lhs rhs linv rinv heq
    simp only [denote_idx_gate heq]
    have := aig.invariant hidx heq
    rw [denote_congr assign1 assign2 aig lhs (by omega) h]
    rw [denote_congr assign1 assign2 aig rhs (by omega) h]

end AIG

end Sat
end Std
