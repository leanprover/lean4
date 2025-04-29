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

-- TODO: should we make this extensible?
private def isBoolEqTarget (declName : Name) : Bool :=
  declName == ``Bool.and ||
  declName == ``Bool.or  ||
  declName == ``Bool.not ||
  declName == ``BEq.beq  ||
  declName == ``decide

builtin_simproc_decl simpBoolEq (@Eq Bool _ _) := fun e => do
  let_expr f@Eq bool lhs rhs ← e | return .continue
  let .const rhsName _ := rhs.getAppFn | return .continue
  if rhsName == ``true || rhsName == ``false then return .continue
  let .const lhsName _ := lhs.getAppFn | return .continue
  if lhsName == ``true || lhsName == ``false then
    -- Just apply comm
    let e' := mkApp3 f bool rhs lhs
    return .visit { expr := e', proof? := mkApp2 (mkConst ``Grind.flip_bool_eq) lhs rhs }
  if isBoolEqTarget lhsName || isBoolEqTarget rhsName then
    -- Convert into `(lhs = true) = (rhs = true)`
    let tr := mkConst ``true
    let e' ← mkEq (mkApp3 f bool lhs tr) (mkApp3 f bool rhs tr)
    return .visit { expr := e', proof? := mkApp2 (mkConst ``Grind.bool_eq_to_prop) lhs rhs }
  return .continue

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
  let s ← addPreMatchCondSimproc s
  let s ← s.add ``simpBoolEq (post := false)
  return #[s]

/-- Returns the simplification context used by `grind`. -/
protected def getSimpContext (config : Grind.Config) : MetaM Simp.Context := do
  let thms ← normExt.getTheorems
  Simp.mkContext
    (config := { arith := true, zeta := config.zeta, zetaDelta := config.zetaDelta })
    (simpTheorems := #[thms])
    (congrTheorems := (← getSimpCongrTheorems))

@[export lean_grind_normalize]
def normalizeImp (e : Expr) (config : Grind.Config) : MetaM Expr := do
  let (r, _) ← Meta.simp e (← Grind.getSimpContext config) (← Grind.getSimprocs)
  return r.expr

end Lean.Meta.Grind
