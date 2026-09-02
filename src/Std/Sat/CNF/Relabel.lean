/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Std.Sat.CNF.Basic
public import Std.Sat.CNF.Sat
import Init.Data.List.Nat.Range

@[expose] public section

namespace Std
namespace Sat

namespace CNF

namespace Clause

/--
Change the literal type in a `Clause` from `α` to `β` by using `r`.
-/
def relabel (r : α → β) (c : Clause α) : Clause β where
  atoms := c.atoms.map r
  polarities := c.polarities
  size_polarities := by rw [c.size_polarities, Array.size_map]
  isBool_polarities := c.isBool_polarities

@[simp]
theorem polarity_relabel {r : α → β} {c : Clause α} {i : Nat} :
    (c.relabel r).polarity i = c.polarity i := rfl

@[simp]
theorem literals_relabel {r : α → β} {c : Clause α} :
    (c.relabel r).literals = c.literals.map (fun (i, n) => (r i, n)) := by
  simp only [literals, relabel, Array.toList_map, List.zipIdx_map, List.map_map]
  apply List.map_congr_left
  intro ⟨x, i⟩ h
  simp [Prod.map, polarity]

@[simp]
theorem relabel_empty (r : α → β) : Clause.relabel r .empty = .empty := by
  apply Clause.ext
  simp

@[simp]
theorem relabel_add (r : α → β) (c : Clause α) :
    Clause.relabel r (c.add atom pol) = (c.relabel r).add (r atom) pol := by
  apply Clause.ext
  simp

@[simp] theorem eval_relabel {r : α → β} {a : β → Bool} {c : Clause α} :
    (relabel r c).eval a = c.eval (a ∘ r) := by
  induction c using inductionOn <;> simp_all

@[simp] theorem relabel_id' : relabel (id : α → α) = id := by
  funext c
  apply Clause.ext
  simp

theorem relabel_congr {c : Clause α} {r1 r2 : α → β} (hw : ∀ v, VarMem v c → r1 v = r2 v) :
    relabel r1 c = relabel r2 c := by
  apply Clause.ext
  simp only [literals_relabel]
  apply List.map_congr_left
  intro ⟨v, p⟩ h
  simp only [Prod.mk.injEq, and_true]
  exact hw v (VarMem_iff_exists_mem_literals.mpr ⟨p, h⟩)

-- We need the unapplied equality later.
@[simp] theorem relabel_relabel' : relabel r1 ∘ relabel r2 = relabel (r1 ∘ r2) := by
  funext c
  apply Clause.ext
  simp [Function.comp_def, List.map_map]

end Clause

/-! ### Relabelling

It is convenient to be able to construct a CNF using a more complicated literal type,
but eventually we need to embed in `Nat`.
-/

/--
Change the literal type in a `CNF` formula from `α` to `β` by using `r`.
-/
def relabel (r : α → β) (f : CNF α) : CNF β := ⟨f.clauses.map (Clause.relabel r)⟩

@[simp] theorem relabel_empty {r : α → β} : relabel r .empty = .empty := by
  simp [relabel, empty]

@[simp] theorem relabel_add {r : α → β} :
    relabel r (f.add c) = (relabel r f).add (c.relabel r) := by
  simp [relabel, add]

@[simp] theorem eval_relabel (r : α → β) (a : β → Bool) (f : CNF α) :
    (relabel r f).eval a = f.eval (a ∘ r) := by
  unfold relabel eval
  simp

@[simp] theorem relabel_append : relabel r (f1 ++ f2) = relabel r f1 ++ relabel r f2 := by
  unfold relabel
  simp [Internal.clauses_append, Internal.ext_iff]

@[simp] theorem relabel_relabel : relabel r1 (relabel r2 f) = relabel (r1 ∘ r2) f := by
  simp only [relabel, Array.map_map, Clause.relabel_relabel']

@[simp] theorem relabel_id : relabel id x = x := by simp [relabel]

theorem relabel_congr {f : CNF α} {r1 r2 : α → β} (hw : ∀ v, VarMem v f → r1 v = r2 v) :
    relabel r1 f = relabel r2 f := by
  dsimp only [relabel]
  rw [Array.map_congr_left]
  intro c h
  apply Clause.relabel_congr
  intro v m
  exact hw _ (VarMem_of (Internal.mem_iff.mpr h) m)

theorem sat_relabel {f : CNF α} (h : Sat (r1 ∘ r2) f) : Sat r1 (relabel r2 f) := by
  simp_all [sat_def]

theorem unsat_relabel {f : CNF α} (r : α → β) (h : Unsat f) :
    Unsat (relabel r f) := by
  simp_all [unsat_def]

private theorem nonempty_or_impossible (f : CNF α) :
    Nonempty α ∨ ∃ n, f = ⟨Array.replicate n .empty⟩ := by
  apply Classical.byContradiction
  intro h
  simp only [Internal.ext_iff, not_or, not_exists] at h
  rcases h with ⟨h1, h2⟩
  specialize h2 f.clauses.size
  simp only [Array.eq_replicate_iff, true_and, Classical.not_forall] at h2
  rcases h2 with ⟨x, ⟨_, hx⟩⟩
  apply h1
  apply Nonempty.intro
  refine (x.literals.head ?_).fst
  simpa using hx

theorem unsat_relabel_iff {f : CNF α} {r : α → β}
    (hw : ∀ {v1 v2}, VarMem v1 f → VarMem v2 f → r v1 = r v2 → v1 = v2) :
    Unsat (relabel r f) ↔ Unsat f := by
  rcases nonempty_or_impossible f with (⟨⟨a₀⟩⟩ | ⟨n, rfl⟩)
  · refine ⟨fun h => ?_, unsat_relabel r⟩
    have em := Classical.propDecidable
    let g : β → α := fun b =>
      if h : ∃ a, VarMem a f ∧ r a = b then h.choose else a₀
    have h' := unsat_relabel g h
    suffices w : relabel g (relabel r f) = f by
      rwa [w] at h'
    have : ∀ a, VarMem a f → g (r a) = a := by
      intro v h
      dsimp [g]
      rw [dite_eq_left ⟨v, h, rfl⟩]
      apply hw _ h
      · exact (Exists.choose_spec (⟨v, h, rfl⟩ : ∃ a', VarMem a' f ∧ r a' = r v)).2
      · exact (Exists.choose_spec (⟨v, h, rfl⟩ : ∃ a', VarMem a' f ∧ r a' = r v)).1
    rw [relabel_relabel, relabel_congr, relabel_id]
    exact this
  · cases n
    · rw [Array.replicate_zero, ← CNF.empty]
      simp
    · rw [Array.replicate_succ, ← CNF.add]
      simp

end CNF

end Sat
end Std
