/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Lean.Elab.BuiltinDo.Basic
meta import Lean.Parser.Do
import Init.Repeat

public section

namespace Lean.Elab.Do

open Lean.Parser.Term
open Lean.Meta

@[builtin_doElem_elab Lean.Parser.Term.doRepeat]
partial def elabDoRepeat : DoElab := fun stx dec => do
  let `(doRepeat| repeat%$tk $seq:doSeq) := stx | throwUnsupportedSyntax
  withRef tk do
  let seqInfo ← inferControlInfoSeq seq
  have mutVars := (← read).mutVars.filter (fun x => seqInfo.reassigns.contains x.getId)
  let (type, breakCont?) ← mkBreakCont dec mutVars seqInfo
  withBreakCont mutVars type breakCont? fun brk => do
  let body ← withLocalDecl `__continue .default type (kind := .implDetail) fun cntVar => do
    let cnt := mkCont mutVars cntVar type
    enterLoopBody brk cnt (← getReturnCont) do
    forallTelescope type fun vars _ => do
      let dec : DoElemCont := {
        resultName := ← mkFreshUserName `__r
        resultType := ← mkPUnit
        k := cnt
        kind := .duplicable
      }
      let body ← elabDoSeq seq dec
      let body ← mkLambdaFVars vars body
      mkLambdaFVars #[cntVar] body
  let u ← getLevel type
  let inst ← mkCCPO type breakCont?.toOption
  mkCont mutVars (mkApp3 (.const ``Lean.Repeat.loop [u]) type inst body) type
where
  mkCCPO (ty : Expr) (brk? : Option Expr) : DoElabM Expr := do
    match ty with
    | .forallE nm t b bi =>
      let u ← getLevel t
      withLocalDecl nm bi t fun var => do
        let b' := b.instantiate1 var
        let v ← getLevel b'
        let inst ← mkCCPO b' (brk?.map (·.app var))
        return mkApp3 (.const ``Lean.Order.instCCPOPi [u, v]) t (.lam nm t b bi)
          (← mkLambdaFVars #[var] inst)
    | _ =>
      -- ty should be `monad.m blockType` now
      let monad := (← read).monadInfo
      let blockType := (← read).doBlockResultType
      let mut nonempty : Expr := default
      if let some brk := brk? then
        nonempty := mkApp2 (.const ``Nonempty.intro [monad.v.succ]) ty brk
      else
        let instType := .app (.const ``Nonempty [monad.v.succ]) ty
        nonempty ← Term.mkInstMVar instType "a terminal repeat loop requires the type to be nonempty"
      let instType := .app (.const ``MonadRepeat [monad.u, monad.v]) monad.m
      let mut inst := .app (.const ``MonadRepeat.defaultInstance [monad.u, monad.v]) monad.m
      if let .some inst' ← trySynthInstance instType then
        inst := inst'
      return mkApp4 (.const ``MonadRepeat.toCCPO [monad.u, monad.v]) monad.m inst blockType nonempty
  mkCont (mutVars : Array Ident) (var : Expr) (ty : Expr) (i : Nat := 0)
      (args : Array Expr := #[]) : DoElabM Expr := do
    if h : i < mutVars.size then
      let .forallE _ t b _ := ty | unreachable!
      let ident := mutVars[i]
      let nm := ident.getId
      let fvar ← getFVarFromUserName nm
      let fvarType ← inferType fvar
      Term.addTermInfo' ident fvar
      let t := t.instantiateRev args
      unless ← isDefEq fvarType t do
        Term.throwTypeMismatchError none t fvarType fvar
      mkCont mutVars var b (i + 1) (args.push fvar)
    else if mutVars.isEmpty then
      return var.app (mkConst ``Unit.unit)
    else
      return mkAppN var args
  mkBreakCont (dec : DoElemCont) (mutVars : Array Ident) (seqInfo : ControlInfo)
      (i : Nat := 0) (vars : Array Expr := #[]) : DoElabM (Expr × Except MessageData Expr) := do
    if h : i < mutVars.size then
      let mutVar := mutVars[i]
      let decl ← getLocalDeclFromUserName mutVar.getId
      withLocalDeclD mutVar.getId decl.type fun var => do
        mkBreakCont dec mutVars seqInfo (i + 1) (vars.push var)
    else
      let monad := (← read).monadInfo.m
      let blockType := (← read).doBlockResultType
      let ty := monad.app blockType
      let ty ← if mutVars.isEmpty then mkArrow (mkConst ``Unit) ty else pure ty
      let ty ← mkForallFVars vars ty
      let mut brk : Except MessageData Expr := .error "Invalid control info, expected no break"
      if seqInfo.breaks then
        let unit ← mkPUnit
        if ← isDefEq dec.resultType unit then
          brk ← Except.ok <$> mkLambdaFVars vars (← dec.continueWithUnit)
          if mutVars.isEmpty then
            brk := brk.map (.lam (← mkFreshUserName `x) (mkConst ``Unit) · .default)
        else
          brk := .error m!"Invalid break from repeat loop, repeat loop is in a terminal \
            position and has an expected type different from {unit}:{indentExpr dec.resultType}"
      else
        dec.elabAsSyntacticallyDeadCode
      return (ty, brk)
  withBreakCont (mutVars : Array Ident) (ty : Expr) (brk? : Except MessageData Expr)
      (k : DoElabM Expr → DoElabM Expr) : DoElabM Expr :=
    match brk? with
    | .error err => k (throwError err)
    | .ok brkValue =>
      withLetDecl `__break ty brkValue (kind := .implDetail) (nondep := true) fun brk => do
        let res ← k (mkCont mutVars brk ty)
        mkLetFVars (generalizeNondepLet := false) #[brk] res
