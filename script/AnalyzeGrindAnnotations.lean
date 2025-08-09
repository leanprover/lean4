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

-- Remark: The following theorems are triggering a `Panic` at `unfoldDefinition?`
-- TODO: fix it
private def toSkip : Std.HashSet Name :=
  Std.HashSet.ofList [``Std.Do.SPred.entails_true_intro, ``Std.Do.SPred.true_intro_simp, ``Std.Do.SPred.conjunction_nil,
   ``Std.Do.SVal.getThe_here, ``Std.Do.SVal.curry_cons, ``Std.Do.SPred.or_cons, ``Std.Do.SVal.uncurry_cons,
   ``Std.Do.SPred.entails_cons, ``Std.Do.SPred.conjunction_cons, ``Std.Do.SPred.imp_cons, ``Std.Do.SVal.curry_uncurry,
   ``Std.Do.SPred.bientails_cons, ``Std.Do.SPred.conjunction_apply, ``Std.Do.SPred.forall_cons,
   ``Std.Do.SPred.iff_cons, ``Std.Do.SVal.getThe_there, ``Std.Do.SPred.not_cons, ``Std.Do.SPred.and_cons
]

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

/-- Analyzes all theorems in the standard library marked as E-matching theorems. -/
def analyzeEMatchTheorems (c : Config := {}) : MetaM Unit := do
  let origins := (← getEMatchTheorems).getOrigins
  for o in origins do
    let .decl declName := o | pure ()
    unless toSkip.contains declName do
      analyzeEMatchTheorem declName c

set_option maxHeartbeats 5000000
run_meta analyzeEMatchTheorems

-- We can analyze specific theorems using commands such as
set_option trace.grind.ematch.instance true in
run_meta analyzeEMatchTheorem ``List.filterMap_some {}
