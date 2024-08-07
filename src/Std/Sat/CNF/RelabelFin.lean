/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
prelude
import Init.Data.List.Nat.Basic
import Std.Sat.CNF.Relabel

namespace Std
namespace Sat

namespace CNF

/--
Obtain the literal with the largest identifier in `c`.
-/
def Clause.maxLiteral (c : Clause Nat) : Option Nat := (c.map (·.1)) |>.maximum?

theorem Clause.of_maxLiteral_eq_some (c : Clause Nat) (h : c.maxLiteral = some maxLit) :
    ∀ lit, mem lit c → lit ≤ maxLit := by
  intro lit hlit
  simp only [maxLiteral, List.maximum?_eq_some_iff', List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at h
  simp only [mem] at hlit
  rcases h with ⟨_, hbar⟩
  cases hlit
  all_goals
    have := hbar (lit, _) (by assumption)
    omega

theorem Clause.maxLiteral_eq_some_of_mem (c : Clause Nat) (h : mem l c)
    : ∃ maxLit, c.maxLiteral = some maxLit := by
  dsimp [mem] at h
  cases h <;> rename_i h
  all_goals
    have h1 := List.ne_nil_of_mem h
    have h2 := not_congr <| @List.maximum?_eq_none_iff _ (c.map (·.1)) _
    simp [← Option.ne_none_iff_exists', h1, h2, maxLiteral]

theorem Clause.of_maxLiteral_eq_none (c : Clause Nat) (h : c.maxLiteral = none) :
    ∀ lit, ¬mem lit c := by
  intro lit hlit
  simp only [maxLiteral, List.maximum?_eq_none_iff, List.map_eq_nil] at h
  simp only [h, not_mem_nil] at hlit

/--
Obtain the literal with the largest identifier in `g`.
-/
def maxLiteral (g : CNF Nat) : Option Nat :=
  List.filterMap Clause.maxLiteral g |>.maximum?

theorem of_maxLiteral_eq_some' (c : CNF Nat) (h : c.maxLiteral = some maxLit) :
    ∀ clause, clause ∈ c → clause.maxLiteral = some localMax → localMax ≤ maxLit := by
  intro clause hclause1 hclause2
  simp [maxLiteral, List.maximum?_eq_some_iff'] at h
  rcases h with ⟨_, hclause3⟩
  apply hclause3 localMax clause hclause1 hclause2

theorem of_maxLiteral_eq_some (c : CNF Nat) (h : c.maxLiteral = some maxLit) :
    ∀ lit, mem lit c → lit ≤ maxLit := by
  intro lit hlit
  dsimp[mem] at hlit
  rcases hlit with ⟨clause, ⟨hclause1, hclause2⟩⟩
  rcases Clause.maxLiteral_eq_some_of_mem clause hclause2 with ⟨localMax, hlocal⟩
  have h1 := of_maxLiteral_eq_some' c h clause hclause1 hlocal
  have h2 := Clause.of_maxLiteral_eq_some clause hlocal lit hclause2
  omega

theorem of_maxLiteral_eq_none (c : CNF Nat) (h : c.maxLiteral = none) :
    ∀ lit, ¬mem lit c := by
  intro lit hlit
  simp only [maxLiteral, List.maximum?_eq_none_iff] at h
  dsimp [mem] at hlit
  rcases hlit with ⟨clause, ⟨hclause1, hclause2⟩⟩
  have := Clause.of_maxLiteral_eq_none clause (List.forall_none_of_filterMap_eq_nil h clause hclause1) lit
  contradiction

/--
An upper bound for the amount of distinct literals in `g`.
-/
def numLiterals (g : CNF Nat) :=
  match g.maxLiteral with
  | none => 0
  | some n => n + 1

theorem lt_numLiterals {g : CNF Nat} (h : mem a g) : a < numLiterals g := by
  dsimp[numLiterals]
  split <;> rename_i h2
  . exfalso
    apply of_maxLiteral_eq_none g h2 a h
  . have := of_maxLiteral_eq_some g h2 a h
    omega

theorem numLiterals_pos {g : CNF Nat} (h : mem a g) : 0 < numLiterals g :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (lt_numLiterals h)

/--
Relabel `g` to a `CNF` formula with a known upper bound for its literals.

This operation might be useful when e.g. using the literals to index into an array of known size
without conducting bounds checks.
-/
def relabelFin (g : CNF Nat) : CNF (Fin g.numLiterals) :=
  if h : ∃ a, mem a g then
    let n := g.numLiterals
    g.relabel fun i =>
      if w : i < n then
        -- This branch will always hold
        ⟨i, w⟩
      else
        ⟨0, numLiterals_pos h.choose_spec⟩
  else
    List.replicate g.length []

theorem unsat_relabelFin {g : CNF Nat} :
    Unsatisfiable (Fin g.numLiterals) g.relabelFin ↔ Unsatisfiable Nat g := by
  dsimp [relabelFin]
  split <;> rename_i h
  · apply unsat_relabel_iff
    intro a b ma mb
    replace ma := lt_numLiterals ma
    replace mb := lt_numLiterals mb
    split <;> rename_i a_lt
    · simp
    · contradiction
  · cases g with
    | nil => simp
    | cons c g =>
      simp only [not_exists_mem] at h
      obtain ⟨n, h⟩ := h
      cases n with
      | zero => simp at h
      | succ n => simp_all [List.replicate_succ]

end CNF

end Sat
end Std
