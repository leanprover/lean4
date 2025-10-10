/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean

namespace Lean.Meta.Grind.Analyzer


/-!
A simple E-matching annotation analyzer.
For each theorem annotated as an E-matching candidate, it creates an artificial goal, executes `grind` and shows the
number of instances created.
For a theorem of the form `params -> type`, the artificial goal is of the form `params -> type -> False`.
-/

/--
`grind` configuration for the analyzer. We disable case-splits and lookahead,
increase the number of generations, and limit the number of instances generated.
-/
def config : Grind.Config := {
  splits       := 0
  lookahead    := false
  mbtc         := false
  ematch       := 20
  instances    := 100
  gen          := 10
}

structure Config where
  /-- Minimum number of instantiations to trigger summary report -/
  min : Nat := 10
  /-- Minimum number of instantiations to trigger detailed report -/
  detailed : Nat := 50

def mkParams : MetaM Params := do
  let params ← Grind.mkParams config
  let ematch ← getEMatchTheorems
  let casesTypes ← Grind.getCasesTypes
  return { params with ematch, casesTypes }

/-- Returns the total number of generated instances.  -/
private def sum (cs : PHashMap Origin Nat) : Nat := Id.run do
  let mut r := 0
  for (_, c) in cs do
    r := r + c
  return r

private def thmsToMessageData (thms : PHashMap Origin Nat) : MetaM MessageData := do
  let data := thms.toArray.filterMap fun (origin, c) =>
    match origin with
    | .decl declName => some (declName, c)
    | _ => none
  let data := data.qsort fun (d₁, c₁) (d₂, c₂) => if c₁ == c₂ then Name.lt d₁ d₂ else c₁ > c₂
  let data ← data.mapM fun (declName, counter) =>
    return .trace { cls := `thm } m!"{.ofConst (← mkConstWithLevelParams declName)} ↦ {counter}" #[]
  return .trace { cls := `thm } "instances" data

/--
Analyzes theorem `declName`. That is, creates the artificial goal based on `declName` type,
and invokes `grind` on it.
-/
def analyzeEMatchTheorem (declName : Name) (c : Config) : MetaM Unit := do
  let info ← getConstInfo declName
  let mvarId ← forallTelescope info.type fun _ type => do
    withLocalDeclD `h type fun _ => do
      return (← mkFreshExprMVar (mkConst ``False)).mvarId!
  let result ← Grind.main mvarId (← mkParams) (pure ())
  let thms := result.counters.thm
  let s := sum thms
  if s > c.min then
    IO.println s!"{declName} : {s}"
  if s > c.detailed then
    logInfo m!"{declName}\n{← thmsToMessageData thms}"

-- Not sure why this is failing: `down_pure` perhaps has an unnecessary universe parameter?
run_meta analyzeEMatchTheorem ``Std.Do.SPred.down_pure {}

/-- Analyzes all theorems in the standard library marked as E-matching theorems. -/
def analyzeEMatchTheorems (c : Config := {}) : MetaM Unit := do
  let origins := (← getEMatchTheorems).getOrigins
  let decls := origins.filterMap fun | .decl declName => some declName | _ => none
  for declName in decls.mergeSort Name.lt do
    try
      analyzeEMatchTheorem declName c
    catch e =>
      logError m!"{declName} failed with {e.toMessageData}"
  logInfo m!"Finished analyzing {decls.length} theorems"

/-- Macro for analyzing E-match theorems with unlimited heartbeats -/
macro "#analyzeEMatchTheorems" : command => `(
  set_option maxHeartbeats 0 in
  run_meta analyzeEMatchTheorems
)

#analyzeEMatchTheorems

-- -- We can analyze specific theorems using commands such as
set_option trace.grind.ematch.instance true

-- 1. grind immediately sees `(#[] : Array α) = ([] : List α).toArray` but probably this should be hidden.
-- 2. `Vector.toArray_empty` keys on `Array.mk []` rather than `#v[].toArray`
-- I guess we could add `(#[].extract _ _).extract _ _` as a stop pattern.
run_meta analyzeEMatchTheorem ``Array.extract_empty {}

-- Neither `Option.bind_some` nor `Option.bind_fun_some` fire, because the terms appear inside
-- lambdas. So we get crazy things like:
-- `fun x => ((some x).bind some).bind fun x => (some x).bind fun x => (some x).bind some`
-- We could consider replacing `filterMap_some` with
-- `filterMap g (filterMap f xs) = filterMap (f >=> g) xs`
-- to avoid the lambda that `grind` struggles with, but this would require more API around the fish.
run_meta analyzeEMatchTheorem ``Array.filterMap_some {}

-- Not entirely certain what is wrong here, but certainly
-- `eq_empty_of_append_eq_empty` is firing too often.
-- Ideally we could instantiate this is we fine `xs ++ ys` in the same equivalence class,
-- note just as soon as we see `xs ++ ys`.
-- I've tried removing this in https://github.com/leanprover/lean4/pull/10162
run_meta analyzeEMatchTheorem ``Array.range'_succ {}

-- Perhaps the same story here.
run_meta analyzeEMatchTheorem ``Array.range_succ {}

-- `zip_map_left` and `zip_map_right` are bad grind lemmas,
-- checking if they can be removed in https://github.com/leanprover/lean4/pull/10163
run_meta analyzeEMatchTheorem ``Array.zip_map {}

-- It seems crazy to me that as soon as we have `0 >>> n = 0`, we instantiate based on the
-- pattern `0 >>> n >>> m` by substituting `0` into `0 >>> n` to produce the `0 >>> n >>> n`.
-- I don't think any forbidden subterms can help us here. I don't know what to do. :-(
run_meta analyzeEMatchTheorem ``Int.zero_shiftRight {}
