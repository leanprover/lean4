/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
import Init.Data.AC
import Lean.Meta.AppBuilder
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Rewrite

namespace Lean.Meta.AC
open Lean.Data.AC
open Lean.Elab.Tactic

abbrev ACExpr := Lean.Data.AC.Expr

structure PreContext where
  id : Nat
  op : Expr
  assoc : Expr
  comm : Option Expr
  idem : Option Expr
  deriving Inhabited

instance : ContextInformation (PreContext × Array Bool) where
  isComm ctx := ctx.1.comm.isSome
  isIdem ctx := ctx.1.idem.isSome
  isNeutral ctx x := ctx.2[x]

instance : EvalInformation PreContext ACExpr where
  arbitrary _ := Data.AC.Expr.var 0
  evalOp _ := Data.AC.Expr.op
  evalVar _ x := Data.AC.Expr.var x

def getInstance (cls : Name) (exprs : Array Expr) : MetaM (Option Expr) := do
  try
    let app ← mkAppM cls exprs
    trace[Meta.AC] "trying: {indentExpr app}"
    let inst ← synthInstance app
    trace[Meta.AC] "got instance"
    return some inst
  catch
  | _ => return none

def preContext (expr : Expr) : MetaM (Option PreContext) := do
  if let some assoc := ←getInstance ``IsAssociative #[expr] then
    return some
      { assoc,
        op := expr
        id := 0
        comm := ←getInstance ``IsCommutative #[expr]
        idem := ←getInstance ``IsIdempotent #[expr] }

  return none

inductive PreExpr
| op (lhs rhs : PreExpr)
| var (e : Expr)

@[matchPattern] def bin {x₁ x₂} (op l r : Expr) :=
  Expr.app (Expr.app op l x₁) r x₂

def toACExpr (op l r : Expr) : MetaM (Array Expr × ACExpr) := do
  let (preExpr, vars) ←
    toPreExpr (mkApp2 op l r)
    |>.run Std.HashSet.empty
  let vars := vars.toArray.insertionSort Expr.lt
  let varMap := vars.foldl (fun xs x => xs.insert x xs.size) Std.HashMap.empty |>.find!

  return (vars, toACExpr varMap preExpr)
  where
    toPreExpr : Expr → StateT ExprSet MetaM PreExpr
    | e@(bin op₂ l r) => do
      if ←isDefEq op op₂ then
        return PreExpr.op (←toPreExpr l) (←toPreExpr r)
      modify fun vars => vars.insert e
      return PreExpr.var e
    | e => do
      modify fun vars => vars.insert e
      return PreExpr.var e

    toACExpr (varMap : Expr → Nat) : PreExpr → ACExpr
    | PreExpr.op l r => Data.AC.Expr.op (toACExpr varMap l) (toACExpr varMap r)
    | PreExpr.var x => Data.AC.Expr.var (varMap x)

def buildNormProof (preContext : PreContext) (l r : Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let (vars, acExpr) ← toACExpr preContext.op l r

  let (isNeutrals, context) ← mkContext vars
  let acExprNormed := Data.AC.evalList ACExpr preContext $ Data.AC.norm (preContext, isNeutrals) acExpr
  let tgt ← convertTarget vars acExprNormed
  let lhs ← convert acExpr
  let rhs ← convert acExprNormed
  let α ← inferType vars[0]
  let u ← getLevel α
  let proof := mkAppN (mkConst ``Context.eq_of_norm [u.dec.get!]) #[α, context, lhs, rhs, ←mkEqRefl (mkConst ``Bool.true)]
  return (proof, tgt)
where
  mkContext (vars : Array Expr) : MetaM (Array Bool × Expr) := do
    let arbitrary := vars[0]

    let vars ← vars.mapM fun x => do
      let isNeutral ←
        match ←getInstance ``IsNeutral #[preContext.op, x] with
        | none => pure (false, ←mkAppOptM ``Option.none #[←mkAppM ``IsNeutral #[preContext.op, x]])
        | some isNeutral => pure (true, ←mkAppM ``Option.some #[isNeutral])

      return (isNeutral.1, ←mkAppM ``Variable.mk #[x, isNeutral.2])

    let (isNeutrals, vars) := vars.unzip
    let vars := vars.toList
    let vars ← mkListLit (←mkAppM ``Variable #[preContext.op]) vars

    let comm ←
      match preContext.comm with
      | none => mkAppOptM ``Option.none #[←mkAppM ``IsCommutative #[preContext.op]]
      | some comm => mkAppM ``Option.some #[comm]

    let idem ←
      match preContext.idem with
      | none => mkAppOptM ``Option.none #[←mkAppM ``IsIdempotent #[preContext.op]]
      | some idem => mkAppM ``Option.some #[idem]

    return (isNeutrals, ←mkAppM ``Lean.Data.AC.Context.mk #[preContext.op, preContext.assoc, comm, idem, vars, arbitrary])

  convert : ACExpr → MetaM Expr
    | Data.AC.Expr.op l r => do mkAppM ``Data.AC.Expr.op #[←convert l, ←convert r]
    | Data.AC.Expr.var x => mkAppM ``Data.AC.Expr.var #[mkNatLit x]

  convertTarget (vars : Array Expr) : ACExpr → MetaM Expr
    | Data.AC.Expr.op l r => do mkAppM' preContext.op #[←convertTarget vars l, ←convertTarget vars r]
    | Data.AC.Expr.var x => return vars[x]

def rewriteUnnormalized (mvarId : MVarId) : MetaM Unit := do
  let simpCtx :=
    {
      simpTheorems  := {}
      congrTheorems := (← getSimpCongrTheorems)
      config        := Simp.neutralConfig
    }
  let tgt ← getMVarType mvarId
  let res ← Simp.main tgt simpCtx (methods := { post })
  let newGoal ← applySimpResultToTarget mvarId tgt res
  applyRefl newGoal
where
  post (e : Expr) : SimpM Simp.Step := do
    let ctx ← read
    match e, ctx.parent? with
    | bin op₁ l r, some (bin op₂ _ _) =>
      if ←isDefEq op₁ op₂ then
        return Simp.Step.done { expr := e }
      match ←preContext op₁ with
      | some pc =>
        let (proof, newTgt) ← buildNormProof pc l r
        return Simp.Step.done { expr := newTgt, proof? := proof }
      | none => return Simp.Step.done { expr := e }
    | bin op l r, _ =>
      match ←preContext op with
      | some pc =>
        let (proof, newTgt) ← buildNormProof pc l r
        return Simp.Step.done { expr := newTgt, proof? := proof }
      | none => return Simp.Step.done { expr := e }
    | e, _ => return Simp.Step.done { expr := e }

@[builtinTactic ac_refl] def ac_refl_tactic : Lean.Elab.Tactic.Tactic := fun stx => do
  let goal ← getMainGoal
  rewriteUnnormalized goal

builtin_initialize
  registerTraceClass `Meta.AC

end Lean.Meta.AC
