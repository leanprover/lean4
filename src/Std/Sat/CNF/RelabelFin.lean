/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.Nat.Order
public import Std.Sat.CNF.Relabel
import Init.Data.Option.Lemmas
import Init.Omega
import Init.Data.List.Impl
import Init.Data.List.MinMax
public import Init.Data.Array.MinMax
import Init.TacticsExtra

@[expose] public section

namespace Std
namespace Sat

namespace CNF

/--
Obtain the literal with the largest identifier in `c`.
-/
def Clause.maxLiteral (c : Clause Nat) : Option Nat := c.atoms.max?

private theorem Clause.maxLiteral_eq {c : Clause Nat} :
    c.maxLiteral = (c.literals.map (·.1)).max? := by
  show c.atoms.max? = _
  rw [← Array.max?_toList, ← Clause.Internal.map_fst_literals]

theorem Clause.of_maxLiteral_eq_some (c : Clause Nat) (h : c.maxLiteral = some maxLit) :
    ∀ lit, VarMem lit c → lit ≤ maxLit := by
  intro lit hlit
  rw [Clause.maxLiteral_eq] at h
  simp only [List.max?_eq_some_iff, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at h
  rw [VarMem_iff_exists_mem_literals] at hlit
  rcases h with ⟨_, hbar⟩
  rcases hlit with ⟨pol, hlit⟩
  have := hbar (lit, pol) hlit
  omega

theorem Clause.maxLiteral_eq_some_of_mem (c : Clause Nat) (h : VarMem l c) :
    ∃ maxLit, c.maxLiteral = some maxLit := by
  rw [VarMem_iff_exists_mem_literals] at h
  rcases h with ⟨pol, h⟩
  have h1 := List.ne_nil_of_mem h
  have h2 := not_congr <| @List.max?_eq_none_iff _ (c.literals.map (·.1)) _
  simp [← Option.ne_none_iff_exists', h1, h2, Clause.maxLiteral_eq]

theorem Clause.of_maxLiteral_eq_none (c : Clause Nat) (h : c.maxLiteral = none) :
    ∀ lit, ¬VarMem lit c := by
  intro lit hlit
  rw [Clause.maxLiteral_eq] at h
  simp only [List.max?_eq_none_iff, List.map_eq_nil_iff] at h
  have : c = .empty := Clause.literals_eq_nil_iff.mp h
  simp only [this, not_VarMem_empty] at hlit

/--
Obtain the literal with the largest identifier in `f`.
-/
def maxLiteral (f : CNF Nat) : Option Nat :=
  f.clauses.filterMap Clause.maxLiteral |>.max?

theorem of_maxLiteral_eq_some' (f : CNF Nat) (h : f.maxLiteral = some maxLit) :
    ∀ (clause : Clause Nat), clause ∈ f → clause.maxLiteral = some localMax → localMax ≤ maxLit := by
  intro clause hclause1 hclause2
  simp [maxLiteral, Array.max?_eq_some_iff] at h
  rcases h with ⟨_, hclause3⟩
  apply hclause3 localMax clause (Internal.mem_iff.mp hclause1) hclause2

theorem of_maxLiteral_eq_some (f : CNF Nat) (h : f.maxLiteral = some maxLit) :
    ∀ lit, VarMem lit f → lit ≤ maxLit := by
  intro lit hlit
  dsimp [VarMem] at hlit
  rcases hlit with ⟨clause, ⟨hclause1, hclause2⟩⟩
  rcases Clause.maxLiteral_eq_some_of_mem clause hclause2 with ⟨localMax, hlocal⟩
  have h1 := of_maxLiteral_eq_some' f h clause (Internal.mem_iff.mpr hclause1) hlocal
  have h2 := Clause.of_maxLiteral_eq_some clause hlocal lit hclause2
  omega

theorem of_maxLiteral_eq_none (f : CNF Nat) (h : f.maxLiteral = none) :
    ∀ lit, ¬VarMem lit f := by
  intro lit hlit
  simp only [maxLiteral, Array.max?_eq_none_iff] at h
  dsimp [VarMem] at hlit
  rcases hlit with ⟨clause, ⟨hclause1, hclause2⟩⟩
  have := Clause.of_maxLiteral_eq_none clause (Array.forall_none_of_filterMap_eq_empty h clause hclause1) lit
  contradiction

/--
An upper bound for the amount of distinct literals in `f`.
-/
def numLiterals (f : CNF Nat) :=
  match f.maxLiteral with
  | none => 0
  | some n => n + 1

theorem lt_numLiterals {f : CNF Nat} (h : VarMem v f) : v < numLiterals f := by
  dsimp [numLiterals]
  split <;> rename_i h2
  · exfalso
    apply of_maxLiteral_eq_none f h2 v h
  · have := of_maxLiteral_eq_some f h2 v h
    omega

theorem numLiterals_pos {f : CNF Nat} (h : VarMem v f) : 0 < numLiterals f :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (lt_numLiterals h)

/--
Relabel `f` to a `CNF` formula with a known upper bound for its literals.

This operation might be useful when e.g. using the literals to index into an array of known size
without conducting bounds checks.
-/
def relabelFin (f : CNF Nat) : CNF (Fin f.numLiterals) :=
  if h : ∃ v, VarMem v f then
    let n := f.numLiterals
    f.relabel fun i =>
      if w : i < n then
        -- This branch will always hold
        ⟨i, w⟩
      else
        ⟨0, numLiterals_pos h.choose_spec⟩
  else
    ⟨Array.replicate f.clauses.size .empty⟩

private theorem not_exists_mem : (¬ ∃ v, VarMem v f) ↔ ∃ n, f.clauses = Array.replicate n .empty := by
  rw [← Internal.any_not_isEmpty_iff_exists_mem]
  simp only [Bool.not_eq_true, Array.any_eq_false', Bool.not_eq_true']
  constructor
  · intro h
    exists f.clauses.size
    rw [Array.eq_replicate_iff]
    refine ⟨rfl, fun c hc => ?_⟩
    have := h c hc
    simpa [List.isEmpty_iff, Clause.literals_eq_nil_iff] using this
  · rintro ⟨n, hn⟩ c hc
    rw [hn, Array.mem_replicate] at hc
    simp [hc.right]

private theorem unsat_replicate_empty_iff {n : Nat} :
    Unsat (⟨Array.replicate n .empty⟩ : CNF α) ↔ n ≠ 0 := by
  constructor
  · intro h hn
    subst hn
    rw [Array.replicate_zero, ← CNF.empty] at h
    exact not_unsat_empty h
  · intro h
    exact unsat_of_mem_unsat (c := .empty) (by simp [Internal.mem_iff, h]) Clause.unsat_empty

@[simp] theorem unsat_relabelFin {f : CNF Nat} : Unsat f.relabelFin ↔ Unsat f := by
  dsimp [relabelFin]
  split <;> rename_i h
  · apply unsat_relabel_iff
    intro a b ma mb
    replace ma := lt_numLiterals ma
    replace mb := lt_numLiterals mb
    split <;> rename_i a_lt
    · simp
    · contradiction
  · rcases not_exists_mem.mp h with ⟨n, hn⟩
    have hf : f = ⟨Array.replicate n .empty⟩ := by rw [Internal.ext_iff, hn]
    subst hf
    simp [unsat_replicate_empty_iff]

end CNF

end Sat
end Std
