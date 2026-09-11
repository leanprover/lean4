/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.CNF.Basic
public import Std.Do.Triple.SpecLemmas

public section

/-!
Hoare triple specifications for `for` loops over `Std.Sat.CNF.Clause`, enabling `mvcgen` to
generate verification conditions for them.
-/

namespace Std.Do

open Std.Sat

universe u₁ u₂ v
variable {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
  {ps : PostShape.{max u₁ u₂}}
variable [Monad m] [WPMonad m ps]

@[spec]
theorem Spec.forIn'_cnfClause
    {xs : CNF.Clause α} {init : β} {f : (a : Literal α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.literals β ps)
    (step : ∀ pref cur suff (h : xs.literals = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [← CNF.Clause.mem_literals_iff, h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.literals, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs.literals, rfl⟩, init))
      (fun b => inv.1 (⟨xs.literals, [], by simp⟩, b), inv.2) := by
  simp only [CNF.Clause.forIn'_eq_forIn'_literals]
  apply Spec.forIn'_list inv step

@[spec]
theorem Spec.forIn_cnfClause
    {xs : CNF.Clause α} {init : β} {f : Literal α → β → m (ForInStep β)}
    (inv : Invariant xs.literals β ps)
    (step : ∀ pref cur suff (h : xs.literals = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.literals, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.literals, rfl⟩, init))
      (fun b => inv.1 (⟨xs.literals, [], by simp⟩, b), inv.2) := by
  simp only [← forIn'_eq_forIn]
  exact Spec.forIn'_cnfClause inv step

end Std.Do
