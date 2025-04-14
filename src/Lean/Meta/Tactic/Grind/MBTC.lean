/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Combinators
import Lean.Meta.Tactic.Grind.Canon

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
  `eqAssignment x y` returns `true` it the theory variables for `x` and `y` have the same
  interpretation/assignment in the target theory. For example, suppose we have the
  constraint `x + y ≤ 0`, and cutsat satified it by assignining both `x` and `y` to
  `0`. Then, `eqAssignment x y` must return `true`.
  -/
  eqAssignment : Expr → Expr → GoalM Bool

private structure ArgInfo where
  arg : Expr
  app : Expr

private abbrev Map := Std.HashMap (Expr × Nat) (List ArgInfo)
private abbrev Candidates := Std.HashSet SplitInfo
private def mkCandidate (a b : ArgInfo) (i : Nat) : GoalM SplitInfo := do
  let (lhs, rhs) := if a.arg.lt b.arg then
    (a.arg, b.arg)
  else
    (b.arg, a.arg)
  let eq ← mkEq lhs rhs
  let eq ← shareCommon (← canon eq)
  return .arg a.app b.app i eq

/-- Model-based theory combination. -/
def mbtc (ctx : MBTC.Context) : GoalM Bool := do
  unless (← getConfig).mbtc do return false
  -- It is pointless to run `mbtc` if maximum number of splits has been reached.
  if (← checkMaxCaseSplit) then return false
  let mut map : Map := {}
  let mut candidates : Candidates := {}
  for ({ expr := e }, _) in (← get).enodes do
    if e.isApp && !e.isEq && !e.isHEq then
    if (← isCongrRoot e) then
    unless (← ctx.isInterpreted e) do
      let f := e.getAppFn
      let mut i := 0
      for arg in e.getAppArgs do
        let some arg ← getRoot? arg | pure ()
        if (← ctx.hasTheoryVar arg) then
          trace[grind.debug.mbtc] "{arg} @ {f}:{i}"
          let argInfo : ArgInfo := { arg, app := e }
          if let some otherInfos := map[(f, i)]? then
            unless otherInfos.any fun info => isSameExpr arg info.arg do
              for otherInfo in otherInfos do
                if (← ctx.eqAssignment arg otherInfo.arg) then
                  if (← hasSameType arg otherInfo.arg) then
                    candidates := candidates.insert (← mkCandidate argInfo otherInfo i)
              map := map.insert (f, i) (argInfo :: otherInfos)
          else
            map := map.insert (f, i) [argInfo]
        i := i + 1
  if candidates.isEmpty then
    return false
  if (← get).split.num > (← getConfig).splits then
    reportIssue "skipping `mbtc`, maximum number of splits has been reached `(splits := {(← getConfig).splits})`"
    return false
  let result := candidates.toArray.qsort fun c₁ c₂ => c₁.lt c₂
  let result ← result.filterMapM fun info => do
    if (← isKnownCaseSplit info) then
      return none
    let .arg a b _ eq := info | return none
    internalize eq (Nat.max (← getGeneration a) (← getGeneration b))
    return some info
  if result.isEmpty then
    return false
  for info in result do
    addSplitCandidate info
  return true

def mbtcTac (ctx : MBTC.Context) : GrindTactic := fun goal => do
  let (r, goal) ← GoalM.run goal do mbtc ctx
  if r then
    return some [goal]
  else
    return none

end Lean.Meta.Grind
