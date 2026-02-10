/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Canon
import Lean.Meta.Tactic.Grind.CastLike
public section
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
  constraint `x + y ≤ 0`, and cutsat satisfied it by assigning both `x` and `y` to
  `0`. Then, `eqAssignment x y` must return `true`.
  -/
  eqAssignment : Expr → Expr → GoalM Bool

private structure ArgInfo where
  arg : Expr
  app : Expr

/-- Key for detecting pairs of terms to case-split on. -/
private structure Key where
  /--
  Mask constructed using the application a term occurs in. It includes
  the function and support arguments.
  We use two auxiliary "fake" terms to create the mask `_main` and `_other`.
  Example suppose we have the application `@Prod.mk Bool Nat flag n`, and we
  are trying to create a key for `n` at this application. The mask will be
  ```
  @Prod.mk Bool Nat _other _main
  ```
  We define "support" in this module as terms using the canonicalizer `isSupport`
  function.
  -/
  mask : Expr
  deriving BEq, Hashable

private def mainMark  := mkConst `__grind_main_arg
private def otherMark := mkConst `__grind_other_arg

private def mkKey (e : Expr) (i : Nat) : MetaM Key :=
  e.withApp fun f args => do
    let info ← getFunInfo f
    let mut args := Array.toVector args
    for h : j in *...args.size do
      let arg := args[j]
      if i == j then
        args := args.set j mainMark
      else if !(← Canon.isSupport info.paramInfo j arg) then
        args := args.set j otherMark
    let mask := mkAppN f args.toArray
    return { mask }

private abbrev Map := Std.HashMap Key (List ArgInfo)
private abbrev Candidates := Std.HashSet SplitInfo
private def mkCandidate (a b : ArgInfo) (i : Nat) : GoalM SplitInfo := do
  let (lhs, rhs) := if a.arg.lt b.arg then
    (a.arg, b.arg)
  else
    (b.arg, a.arg)
  let eq ← mkEq lhs rhs
  let eq ← shareCommon (← canon eq)
  return .arg a.app b.app i eq (.mbtc a.app b.app i)

/-- Returns `true` if `f` is a type class instance -/
private def isFnInstance (f : Expr) : CoreM Bool := do
  let .const declName _ := f | return false
  isInstanceReducible declName

/-- Model-based theory combination. -/
def mbtc (ctx : MBTC.Context) : GoalM Bool := do
  unless (← getConfig).mbtc do return false
  -- It is pointless to run `mbtc` if maximum number of splits has been reached.
  if (← checkMaxCaseSplit) then return false
  let mut map : Map := {}
  let mut candidates : Candidates := {}
  for e in (← get).exprs do
    if e.isApp && !e.isEq && !e.isHEq then
    if (← isCongrRoot e) then
    unless (← ctx.isInterpreted e) do
      let f := e.getAppFn
      /-
      Remark: we ignore type class instances and cast-like applications in model-based theory combination.
      `grind` treats instances as support elements, and they are handled by the canonicalizer.
      cast-like internal operations and handled by their associated solver.
      -/
      if !(← isFnInstance f) && !isCastLikeFn f then
        let mut i := 0
        for arg in e.getAppArgs do
          let some arg ← getRoot? arg | pure ()
          if (← ctx.hasTheoryVar arg) then
            trace[grind.debug.mbtc] "{arg} @ {f}:{i}"
            let argInfo : ArgInfo := { arg, app := e }
            let key ← mkKey e i
            if let some otherInfos := map[key]? then
              unless otherInfos.any fun info => isSameExpr arg info.arg do
                for otherInfo in otherInfos do
                  if (← ctx.eqAssignment arg otherInfo.arg) then
                    if (← hasSameType arg otherInfo.arg) then
                      candidates := candidates.insert (← mkCandidate argInfo otherInfo i)
                map := map.insert key (argInfo :: otherInfos)
            else
              map := map.insert key [argInfo]
          i := i + 1
  if candidates.isEmpty then
    return false
  if (← get).split.num > (← getConfig).splits then
    reportIssue! "skipping `mbtc`, maximum number of splits has been reached `(splits := {(← getConfig).splits})`"
    return false
  let result := candidates.toArray.qsort fun c₁ c₂ => c₁.lt c₂
  let result ← result.filterMapM fun info => do
    if (← isKnownCaseSplit info) then
      return none
    let .arg a b _ eq _ := info | return none
    trace[grind.mbtc] "{eq}"
    internalize eq (Nat.max (← getGeneration a) (← getGeneration b))
    return some info
  if result.isEmpty then
    return false
  for info in result do
    addSplitCandidate info
  return true

end Lean.Meta.Grind
