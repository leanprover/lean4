/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind

/--
Model-based theory combination context.
-/
structure MBTC.Context where
  /--
  `isInterpreted e` returns `true` if `e` is an interpreted symbol in the target theory.
  Example: `+` for cutsat
  -/
  isInterpreted : Expr → GoalM Bool
  /--
  `hasTheoryVar e` returns `true` if `e` has a theory variable in the target theory.
  For example, suppose we have the constraint `x + y ≤ 0`, then `x` and `y` have theory
  vars in the cutsat procedure.
  -/
  hasTheoryVar : Expr → GoalM Bool
  /--
  `eqAssignment a b` returns `true` it the theory variables for `x` and `y` have the same
  interpretation/assignment in the target theory. For example, suppose we have the
  constraint `x + y ≤ 0`, and cutsat satified it by assignining both `x` and `y` to
  `0`. Then, `eqAssignment x y` must return `true`.
  -/
  eqAssignment : Expr → Expr → GoalM Bool

private abbrev Map := Std.HashMap (Expr × Nat) (List Expr)
private abbrev Candidates := Std.HashSet (Expr × Expr)
private def mkCandidateKey (a b : Expr) : Expr × Expr :=
  if a.lt b then
    (a, b)
  else
    (b, a)

/-- Model-based theory combination. -/
def mbtc (ctx : MBTC.Context) : GoalM (Array (Expr × Expr)) := do
  let mut map : Map := {}
  let mut candidates : Candidates := {}
  for ({ expr := e }, _) in (← get).enodes do
    if e.isApp then
    if (← isCongrRoot e) then
    unless (← ctx.isInterpreted e) do
      let f := e.getAppFn
      let mut i := 0
      for arg in e.getAppArgs do
        let arg ← getRoot arg
        if (← ctx.hasTheoryVar arg) then
          if let some others := map[(f, i)]? then
            unless others.any (isSameExpr arg ·) do
              for other in others do
                unless (← ctx.eqAssignment arg other) do
                  let k := mkCandidateKey arg other
                  candidates := candidates.insert k
              map := map.insert (f, i) (arg :: others)
          else
            map := map.insert (f, i) [arg]
        i := i + 1
  let result := candidates.toArray.qsort fun (a₁, b₁) (a₂, b₂) =>
    if isSameExpr a₁ a₂ then
      b₁.lt b₂
    else
      a₁.lt a₂
  return result

end Lean.Meta.Grind
