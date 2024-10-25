/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.LawfulOperator
import Std.Sat.AIG.RefVec

namespace Std
namespace Sat

namespace AIG

variable {α : Type} [Hashable α] [DecidableEq α]

class LawfulVecOperator (α : Type) [Hashable α] [DecidableEq α]
    (β : AIG α → Nat → Type) (f : {len : Nat} → (aig : AIG α) → β aig len → RefVecEntry α len) where
  le_size : ∀ (aig : AIG α) (input : β aig len), aig.decls.size ≤ (f aig input).aig.decls.size
  decl_eq : ∀ (aig : AIG α) (input : β aig len) (idx : Nat) (h1 : idx < aig.decls.size) (h2),
    (f aig input).aig.decls[idx]'h2 = aig.decls[idx]'h1

namespace LawfulVecOperator

variable {β : AIG α → Nat → Type}
variable {f : {len : Nat} → (aig : AIG α) → β aig len → RefVecEntry α len}
variable [LawfulVecOperator α β f]

theorem isPrefix_aig (aig : AIG α) (input : β aig len) :
    IsPrefix aig.decls (f aig input).aig.decls := by
  apply IsPrefix.of
  · intro idx h
    apply decl_eq
  · apply le_size

theorem lt_size (entry : Entrypoint α) (input : β entry.aig len) :
    entry.ref.gate < (f entry.aig input).aig.decls.size := by
  have h1 := entry.ref.hgate
  have h2 : entry.aig.decls.size ≤ (f entry.aig input).aig.decls.size := by
    apply le_size
  omega

theorem lt_size_of_lt_aig_size (aig : AIG α) (input : β aig len) (h : x < aig.decls.size) :
    x < (f aig input).aig.decls.size := by
  apply Nat.lt_of_lt_of_le
  · exact h
  · exact le_size aig input

theorem le_size_of_le_aig_size (aig : AIG α) (input : β aig len) (h : x ≤ aig.decls.size) :
    x ≤ (f aig input).aig.decls.size := by
  apply Nat.le_trans
  · exact h
  · exact le_size aig input

@[simp]
theorem denote_input_entry (entry : Entrypoint α) {input : β entry.aig len} {h} :
    ⟦(f entry.aig input).aig, ⟨entry.ref.gate, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_isPrefix
  apply isPrefix_aig

@[simp]
theorem denote_cast_entry (entry : Entrypoint α) {input : β entry.aig len} {h} :
    ⟦(f entry.aig input).aig, entry.ref.cast h, assign⟧
      =
    ⟦entry, assign⟧ := by
  simp [Ref.cast]

theorem denote_mem_prefix {aig : AIG α} {input : β aig len} (h) :
    ⟦(f aig input).aig, ⟨start, by apply lt_size_of_lt_aig_size; omega⟩, assign⟧
      =
    ⟦aig, ⟨start, h⟩, assign⟧ :=  by
  rw [denote_input_entry ⟨aig, start, h⟩]

@[simp]
theorem denote_input_vec (s : RefVecEntry α len) {input : β s.aig len} {hcast} :
    ⟦(f s.aig input).aig, (s.vec.get idx hidx).cast hcast, assign⟧
      =
    ⟦s.aig, s.vec.get idx hidx, assign⟧ :=  by
  rw [denote_mem_prefix]
  rfl

end LawfulVecOperator
end AIG

end Sat
end Std
