/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.Basic
import Std.Sat.AIG.Lemmas

namespace Std
namespace Sat

namespace AIG

namespace Decl

def relabel (r : α → β) (decl : Decl α) : Decl β :=
  match decl with
  | .false => .false
  | .atom a => .atom (r a)
  | .gate lhs rhs => .gate lhs rhs

theorem relabel_id_map (decl : Decl α) : relabel id decl = decl := by
  simp only [relabel, id_eq]
  cases decl <;> rfl

theorem relabel_comp (decl : Decl α) (g : α → β) (h : β → γ) :
    relabel (h ∘ g) decl = relabel h (relabel g decl) := by
  cases decl <;> rfl

theorem relabel_false {decls : Array (Decl α)} {r : α → β} {hidx : idx < decls.size}
    (h : relabel r decls[idx] = .false) :
    decls[idx] = .false := by
  unfold relabel at h
  split at h <;> simp_all

theorem relabel_atom {decls : Array (Decl α)} {r : α → β} {hidx : idx < decls.size}
    (h : relabel r decls[idx] = .atom a) :
    ∃ x, decls[idx] = .atom x ∧ a = r x := by
  unfold relabel at h
  split at h
  · contradiction
  · next x heq =>
    injection h with h
    exists x
    simp [heq, h]
  · contradiction

theorem relabel_gate {decls : Array (Decl α)} {r : α → β} {hidx : idx < decls.size}
    (h : relabel r decls[idx] = .gate lhs rhs) :
    decls[idx] = (.gate lhs rhs : Decl α) := by
  unfold relabel at h
  split at h <;> simp_all

end Decl

variable {α : Type} [Hashable α] [DecidableEq α]
variable {β : Type} [Hashable β] [DecidableEq β]

def relabel (r : α → β) (aig : AIG α) : AIG β :=
  let decls := aig.decls.map (Decl.relabel r)
  let cache := Cache.empty
  {
    decls,
    cache,
    hdag := by
      intro idx lhs rhs hbound hgate
      simp +zetaDelta [decls] at hgate
      have := Decl.relabel_gate hgate
      apply aig.hdag
      assumption
    hzero := by simp [decls, aig.hzero]
    hconst := by simp [decls, aig.hconst, Decl.relabel]
  }

@[simp]
theorem relabel_size_eq_size {aig : AIG α} {r : α → β} :
    (aig.relabel r).decls.size = aig.decls.size := by
  simp [relabel]

theorem relabel_false {aig : AIG α} {r : α → β} {hidx : idx < (relabel r aig).decls.size}
    (h : (relabel r aig).decls[idx]'hidx = .false) :
    aig.decls[idx]'(by rw [← relabel_size_eq_size (r := r)]; omega) = .false := by
  apply Decl.relabel_false
  simpa [relabel] using h


theorem relabel_atom {aig : AIG α} {r : α → β} {hidx : idx < (relabel r aig).decls.size}
    (h : (relabel r aig).decls[idx]'hidx = .atom a) :
    ∃ x, aig.decls[idx]'(by rw [← relabel_size_eq_size (r := r)]; omega) = .atom x ∧ a = r x := by
  apply Decl.relabel_atom
  simpa [relabel] using h

theorem relabel_gate {aig : AIG α} {r : α → β} {hidx : idx < (relabel r aig).decls.size}
    (h : (relabel r aig).decls[idx]'hidx = .gate lhs rhs) :
    aig.decls[idx]'(by rw [← relabel_size_eq_size (r := r)]; omega) = .gate lhs rhs := by
  apply Decl.relabel_gate
  simpa [relabel] using h

@[simp]
theorem denote_relabel (aig : AIG α) (r : α → β) (start : Nat) {hidx}
    (assign : β → Bool) :
    ⟦aig.relabel r, ⟨start, invert, hidx⟩, assign⟧
      =
    ⟦aig, ⟨start, invert, by rw [← relabel_size_eq_size (r := r)]; omega⟩, (assign ∘ r)⟧ := by
  apply denote_idx_trichotomy
  · intro heq1
    have heq2 := relabel_false heq1
    rw [denote_idx_false heq1]
    rw [denote_idx_false heq2]
  · intro a heq1
    rw [denote_idx_atom heq1]
    rcases relabel_atom heq1 with ⟨x, ⟨hlx, hrx⟩⟩
    rw [hrx] at heq1
    rw [denote_idx_atom hlx]
    simp [hrx]
  · intro lhs rhs heq1
    have heq2 := relabel_gate heq1
    rw [denote_idx_gate heq1]
    rw [denote_idx_gate heq2]
    have := aig.hdag (by rw [← relabel_size_eq_size (r := r)]; omega) heq2
    rw [denote_relabel aig r lhs.gate assign]
    rw [denote_relabel aig r rhs.gate assign]

theorem unsat_relabel {aig : AIG α} (r : α → β) {hidx} :
    aig.UnsatAt idx invert hidx → (aig.relabel r).UnsatAt idx invert (by simp [hidx]) := by
  intro h assign
  specialize h (assign ∘ r)
  simp [h]

theorem relabel_unsat_iff [Nonempty α] {aig : AIG α} {r : α → β} {hidx1} {hidx2}
    (hinj : ∀ x y, x ∈ aig → y ∈ aig → r x = r y → x = y) :
    (aig.relabel r).UnsatAt idx invert hidx1 ↔ aig.UnsatAt idx invert hidx2 := by
  constructor
  · intro h assign
    let g : β → α := fun b =>
      have em := Classical.propDecidable
      if h : ∃ a, a ∈ aig ∧ r a = b then h.choose else Classical.choice inferInstance
    have h' := unsat_relabel g h
    specialize h' assign
    simp only [denote_relabel] at h'
    rw [← h']
    apply denote_congr
    · intro a hmem
      simp only [Function.comp_apply, g]
      split
      · next h =>
        rcases Exists.choose_spec h with ⟨_, heq⟩
        specialize hinj _ _ (by assumption) (by assumption) heq
        simp [hinj]
      · next h =>
        simp only [not_exists, not_and] at h
        specialize h a hmem
        contradiction
  · apply unsat_relabel

namespace Entrypoint

def relabel (r : α → β) (entry : Entrypoint α) : Entrypoint β :=
  { entry with
    aig := entry.aig.relabel r
    ref.hgate := by simp [entry.ref.hgate]
  }

@[simp]
theorem relabel_size_eq {entry : Entrypoint α} {r : α → β} :
    (entry.relabel r).aig.decls.size = entry.aig.decls.size := by
  simp [relabel]

theorem relabel_unsat_iff [Nonempty α] {entry : Entrypoint α} {r : α → β}
    (hinj : ∀ x y, x ∈ entry.aig → y ∈ entry.aig → r x = r y → x = y) :
    (entry.relabel r).Unsat ↔ entry.Unsat := by
  simp [relabel, Unsat]
  rw [AIG.relabel_unsat_iff]
  assumption

end Entrypoint
end AIG
