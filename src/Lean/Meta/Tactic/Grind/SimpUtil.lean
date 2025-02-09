/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.MatchDiscrOnly
import Lean.Meta.Tactic.Grind.MatchCond
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.List

namespace Lean.Meta.Grind

builtin_initialize normExt : SimpExtension ← mkSimpExt

def registerNormTheorems (preDeclNames : Array Name) (postDeclNames : Array Name) : MetaM Unit := do
  let thms ← normExt.getTheorems
  unless thms.lemmaNames.isEmpty do
    throwError "`grind` normalization theorems have already been initialized"
  for declName in preDeclNames do
    addSimpTheorem normExt declName (post := false) (inv := false) .global (eval_prio default)
  for declName in postDeclNames do
    addSimpTheorem normExt declName (post := true) (inv := false) .global (eval_prio default)

/-- Returns the array of simprocs used by `grind`. -/
protected def getSimprocs : MetaM (Array Simprocs) := do
  let s ← Simp.getSEvalSimprocs
  /-
  We don't want to apply `List.reduceReplicate` as a normalization operation in
  `grind`. Consider the following example:
  ```
  example (ys : List α) : n = 0 → List.replicate n ys = [] := by
    grind only [List.replicate]
  ```
  The E-matching module generates the following instance for `List.replicate.eq_1`
  ```
  List.replicate 0 [] = []
  ```
  We don't want it to be simplified to `[] = []`.
  -/
  let s := s.erase ``List.reduceReplicate
  let s ← addSimpMatchDiscrsOnly s
  let s ← addMatchCond s
  return #[s]

/-- Returns the simplification context used by `grind`. -/
protected def getSimpContext : MetaM Simp.Context := do
  let thms ← normExt.getTheorems
  Simp.mkContext
    (config := { arith := true })
    (simpTheorems := #[thms])
    (congrTheorems := (← getSimpCongrTheorems))

@[export lean_grind_normalize]
def normalizeImp (e : Expr) : MetaM Expr := do
  let (r, _) ← Meta.simp e (← Grind.getSimpContext) (← Grind.getSimprocs)
  return r.expr

end Lean.Meta.Grind
