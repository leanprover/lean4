/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.LRAT.Internal.LRATChecker
public import Std.Tactic.BVDecide.LRAT.Internal.Formula.Implementation
public import Std.Tactic.BVDecide.LRAT.Internal.Formula.Instance
public import Std.Tactic.BVDecide.LRAT.Internal.Actions


@[expose] public section

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

/-!
This module implements an LRAT checker that acts on an `Array IntAction` and only explodes it into
the `DefaultClauseAction` when required instead of upfront. This allows for a significantly smaller
memory footprint compared to the generic LRAT checker.
-/

def compactLratChecker (f : DefaultFormula n) (proof : Array IntAction) :
    Result :=
  go f proof 0
where
  go {n : Nat} (f : DefaultFormula n) (proof : Array IntAction) (idx : Nat) : Result :=
    if h : idx < proof.size then
      let step := intActionToDefaultClauseAction n proof[idx]
      match step with
      | none => go f proof (idx + 1)
      | some (.addEmpty _ rupHints) =>
        let (_, checkSuccess) := Formula.performRupAdd f Clause.empty rupHints
        if checkSuccess then
          .success
        else
          .rupFailure
      | some (.addRup _ c rupHints) =>
        let (f, checkSuccess) := Formula.performRupAdd f c rupHints
        if checkSuccess then
          go f proof (idx + 1)
        else
          .rupFailure
      | some (.addRat _ c pivot rupHints ratHints) =>
        if pivot ∈ Clause.toList c then
          let (f, checkSuccess) := Formula.performRatAdd f c pivot rupHints ratHints
          if checkSuccess then
            go f proof (idx + 1)
          else
            .rupFailure
        else
          go f proof (idx + 1)
      | some (.del ids) => go (Formula.delete f ids) proof (idx + 1)
    else
      .outOfProof

end Internal
end LRAT
end Std.Tactic.BVDecide
