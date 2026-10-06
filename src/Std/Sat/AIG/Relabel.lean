/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.AIG.Lemmas
import Init.ByCases
import Init.Omega

@[expose] public section

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
  next x heq =>
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

/--
Relabel the atoms of `aig` with `r`. To enforce sharing of the atoms `r` must be injective.
-/
def relabel (r : α → β) (aig : AIG α) (hinj : ∀ x y, x ∈ aig → y ∈ aig → r x = r y → x = y) :
    AIG β :=
  let decls := aig.decls.map (Decl.relabel r)
  have huniq : ∀ (i j : Nat) (hi : i < decls.size) (hj : j < decls.size) (b : β),
      decls[i] = .atom b → decls[j] = .atom b → i = j := by
    intro i j hi hj b hi' hj'
    simp only [decls, Array.size_map] at hi hj
    simp only [decls, Array.getElem_map] at hi' hj'
    rcases Decl.relabel_atom hi' with ⟨x, hx, hbx⟩
    rcases Decl.relabel_atom hj' with ⟨y, hy, hby⟩
    have hmemx : x ∈ aig := by rw [mem_def]; exact Array.mem_of_getElem hx
    have hmemy : y ∈ aig := by rw [mem_def]; exact Array.mem_of_getElem hy
    have := hinj x y hmemx hmemy (by rw [← hbx, ← hby])
    subst this
    exact aig.atom_unique hx hy
  {
    decls,
    cache := Cache.ofAtoms decls huniq,
    hdag := by
      intro idx lhs rhs hbound hgate
      simp +zetaDelta at hgate
      have := Decl.relabel_gate hgate
      apply aig.hdag
      assumption
    hzero := by simp [decls, aig.hzero]
    hconst := by simp [decls, aig.hconst, Decl.relabel]
  }

@[simp]
theorem relabel_size_eq_size {aig : AIG α} {r : α → β} {hinj} :
    (aig.relabel r hinj).decls.size = aig.decls.size := by
  simp [relabel]

theorem relabel_false {aig : AIG α} {r : α → β} {hinj} {hidx : idx < (relabel r aig hinj).decls.size}
    (h : (relabel r aig hinj).decls[idx]'hidx = .false) :
    aig.decls[idx]'(by rw [← relabel_size_eq_size (r := r) (hinj := hinj)]; omega) = .false := by
  apply Decl.relabel_false
  simpa [relabel] using h

theorem relabel_atom {aig : AIG α} {r : α → β} {hinj} {hidx : idx < (relabel r aig hinj).decls.size}
    (h : (relabel r aig hinj).decls[idx]'hidx = .atom a) :
    ∃ x, aig.decls[idx]'(by rw [← relabel_size_eq_size (r := r) (hinj := hinj)]; omega) = .atom x ∧ a = r x := by
  apply Decl.relabel_atom
  simpa [relabel] using h

theorem relabel_gate {aig : AIG α} {r : α → β} {hinj} {hidx : idx < (relabel r aig hinj).decls.size}
    (h : (relabel r aig hinj).decls[idx]'hidx = .gate lhs rhs) :
    aig.decls[idx]'(by rw [← relabel_size_eq_size (r := r) (hinj := hinj)]; omega) = .gate lhs rhs := by
  apply Decl.relabel_gate
  simpa [relabel] using h

@[simp]
theorem denote_relabel (aig : AIG α) (r : α → β) {hinj} (start : Nat) {hidx}
    (assign : β → Bool) :
    ⟦aig.relabel r hinj, ⟨start, invert, hidx⟩, assign⟧
      =
    ⟦aig, ⟨start, invert, by rw [← relabel_size_eq_size (r := r) (hinj := hinj)]; omega⟩, (assign ∘ r)⟧ := by
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
    have := aig.hdag (by rw [← relabel_size_eq_size (r := r) (hinj := hinj)]; omega) heq2
    rw [denote_relabel aig r lhs.gate assign]
    rw [denote_relabel aig r rhs.gate assign]

theorem unsat_relabel {aig : AIG α} (r : α → β) {hinj} {hidx} :
    aig.UnsatAt idx invert hidx → (aig.relabel r hinj).UnsatAt idx invert (by simp [hidx]) := by
  intro h assign
  specialize h (assign ∘ r)
  simp [h]

theorem relabel_unsat_iff_of_not_Nonempty {aig : AIG α}
    {r : α → β} {hinj} {hidx1} {hidx2}
    (hNonempty : ¬ Nonempty α) :
    (aig.relabel r hinj).UnsatAt idx invert hidx1 ↔ aig.UnsatAt idx invert hidx2 := by
  constructor
  · intro hα assignα
    let assignβ : β → Bool := fun b => false
    specialize hα assignβ
    have hAssignα : assignα  = assignβ ∘ r := by
      ext a
      apply hNonempty (Nonempty.intro a) |>.elim
    rw [hAssignα, ← denote_relabel, ← hα]
  · apply unsat_relabel

theorem relabel_unsat_iff_of_Nonempty [Nonempty α] {aig : AIG α} {r : α → β} {hinj} {hidx1}
    {hidx2} :
    (aig.relabel r hinj).UnsatAt idx invert hidx1 ↔ aig.UnsatAt idx invert hidx2 := by
  constructor
  · intro h assign
    let g : β → α := fun b =>
      have em := Classical.propDecidable
      if h : ∃ a, a ∈ aig ∧ r a = b then h.choose else Classical.choice inferInstance
    specialize h (assign ∘ g)
    simp only [denote_relabel] at h
    rw [← h]
    apply denote_congr
    · intro a hmem
      simp only [Function.comp_apply, g]
      split
      next h =>
        rcases Exists.choose_spec h with ⟨_, heq⟩
        specialize hinj _ _ (by assumption) (by assumption) heq
        simp [hinj]
      next h =>
        simp only [not_exists, not_and] at h
        specialize h a hmem
        contradiction
  · apply unsat_relabel

/--
`relabel` preserves unsatisfiablility.
-/
theorem relabel_unsat_iff {aig : AIG α} {r : α → β} {hinj} {hidx1} {hidx2} :
    (aig.relabel r hinj).UnsatAt idx invert hidx1 ↔ aig.UnsatAt idx invert hidx2 := by
  by_cases hαNonempty : Nonempty α
  · apply relabel_unsat_iff_of_Nonempty
  · apply relabel_unsat_iff_of_not_Nonempty hαNonempty

namespace Entrypoint

def relabel (r : α → β) (entry : Entrypoint α)
    (hinj : ∀ x y, x ∈ entry.aig → y ∈ entry.aig → r x = r y → x = y) : Entrypoint β :=
  { entry with
    aig := entry.aig.relabel r hinj
    ref.hgate := by simp [entry.ref.hgate]
  }

@[simp]
theorem relabel_size_eq {entry : Entrypoint α} {r : α → β} {hinj} :
    (entry.relabel r hinj).aig.decls.size = entry.aig.decls.size := by
  simp [relabel]

theorem relabel_unsat_iff {entry : Entrypoint α} {r : α → β} {hinj} :
    (entry.relabel r hinj).Unsat ↔ entry.Unsat := by
  simp [relabel, Unsat]
  rw [AIG.relabel_unsat_iff]

end Entrypoint
end AIG
