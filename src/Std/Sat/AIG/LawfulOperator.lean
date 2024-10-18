/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.Basic

/-!
The lawful operator framework provides free theorems around the typeclass `LawfulOperator`.
Its definition is based on section 3.3 of the AIGNET paper.
-/

namespace Std
namespace Sat

namespace AIG

/--
`decls1` is a prefix of `decls2`
-/
structure IsPrefix (decls1 decls2 : Array (Decl α)) : Prop where
  of ::
    /--
    The prefix may never be longer than the other array.
    -/
    size_le : decls1.size ≤ decls2.size
    /--
    The prefix and the other array must agree on all elements up until the bound of the prefix
    -/
    idx_eq : ∀ idx (h : idx < decls1.size), decls2[idx]'(by omega) = decls1[idx]'h

/--
If `decls1` is a prefix of `decls2` and we start evaluating `decls2` at an
index in bounds of `decls1` we can evaluate at `decls1`.
-/
theorem denote.go_eq_of_isPrefix (decls1 decls2 : Array (Decl α)) (start : Nat) {hdag1} {hdag2}
    {hbounds1} {hbounds2} (hprefix : IsPrefix decls1 decls2) :
    denote.go start decls2 assign hbounds2 hdag2
      =
    denote.go start decls1 assign hbounds1 hdag1 := by
  unfold denote.go
  have hidx1 := hprefix.idx_eq start hbounds1
  split
  · next heq =>
    rw [hidx1] at heq
    split <;> simp_all
  · next heq =>
    rw [hidx1] at heq
    split <;> simp_all
  · next lhs rhs linv rinv heq =>
    rw [hidx1] at heq
    have := hdag1 hbounds1 heq
    have hidx2 := hprefix.idx_eq lhs (by omega)
    have hidx3 := hprefix.idx_eq rhs (by omega)
    split
    · simp_all
    · simp_all
    · simp_all
      congr 2
      · apply denote.go_eq_of_isPrefix
        assumption
      · apply denote.go_eq_of_isPrefix
        assumption
termination_by start

variable {α : Type} [Hashable α] [DecidableEq α]

@[inherit_doc denote.go_eq_of_isPrefix]
theorem denote.eq_of_isPrefix (entry : Entrypoint α) (newAIG : AIG α)
      (hprefix : IsPrefix entry.aig.decls newAIG.decls) :
    ⟦newAIG, ⟨entry.ref.gate, (by have := entry.ref.hgate; have := hprefix.size_le; omega)⟩, assign⟧
      =
    ⟦entry, assign⟧
    := by
  unfold denote
  apply denote.go_eq_of_isPrefix
  assumption

abbrev ExtendingEntrypoint (aig : AIG α) : Type :=
  { entry : Entrypoint α // aig.decls.size ≤ entry.aig.decls.size }

abbrev ExtendingRefVecEntry (aig : AIG α) (len : Nat) : Type :=
  { ref : RefVecEntry α len // aig.decls.size ≤ ref.aig.decls.size }

/--
A function `f` that takes some `aig : AIG α` and an argument of type `β aig` is called a lawful
AIG operator if it only extends the `AIG` but never modifies already existing nodes.

This guarantees that applying such a function will not change the semantics of any existing parts
of the circuit, allowing us to perform local reasoning on the AIG.
-/
class LawfulOperator (α : Type) [Hashable α] [DecidableEq α]
    (β : AIG α → Type) (f : (aig : AIG α) → β aig → Entrypoint α)  where
  le_size : ∀ (aig : AIG α) (input : β aig), aig.decls.size ≤ (f aig input).aig.decls.size
  decl_eq : ∀ (aig : AIG α) (input : β aig) (idx : Nat) (h1 : idx < aig.decls.size) (h2),
    (f aig input).aig.decls[idx]'h2 = aig.decls[idx]'h1

namespace LawfulOperator

variable {β : AIG α → Type}
variable {f : (aig : AIG α) → β aig → Entrypoint α} [LawfulOperator α β f]

theorem isPrefix_aig (aig : AIG α) (input : β aig) :
    IsPrefix aig.decls (f aig input).aig.decls := by
  apply IsPrefix.of
  · intro idx h
    apply decl_eq
  · apply le_size

theorem lt_size (entry : Entrypoint α) (input : β entry.aig) :
    entry.ref.gate < (f entry.aig input).aig.decls.size := by
  have h1 := entry.ref.hgate
  have h2 : entry.aig.decls.size ≤ (f entry.aig input).aig.decls.size := by
    apply le_size
  omega

theorem lt_size_of_lt_aig_size (aig : AIG α) (input : β aig) (h : x < aig.decls.size) :
    x < (f aig input).aig.decls.size := by
  apply Nat.lt_of_lt_of_le
  · exact h
  · exact le_size aig input

theorem le_size_of_le_aig_size (aig : AIG α) (input : β aig) (h : x ≤ aig.decls.size) :
    x ≤ (f aig input).aig.decls.size := by
  apply Nat.le_trans
  · exact h
  · exact le_size aig input

@[simp]
theorem denote_input_entry (entry : Entrypoint α) {input} {h} :
    ⟦(f entry.aig input).aig, ⟨entry.ref.gate, h⟩, assign⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_isPrefix
  apply isPrefix_aig

@[simp]
theorem denote_cast_entry (entry : Entrypoint α) {input} {h} :
    ⟦(f entry.aig input).aig, entry.ref.cast h, assign⟧
      =
    ⟦entry, assign⟧ := by
  simp [Ref.cast]

theorem denote_mem_prefix {aig : AIG α} {input} (h) :
    ⟦(f aig input).aig, ⟨start, by apply lt_size_of_lt_aig_size; omega⟩, assign⟧
      =
    ⟦aig, ⟨start, h⟩, assign⟧ :=  by
  rw [denote_input_entry ⟨aig, start, h⟩]

end LawfulOperator

end AIG

end Sat
end Std
