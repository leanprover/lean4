/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Simp.Main
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
  isNeutral ctx x := ctx.2[x]!

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

@[match_pattern] def bin (op l r : Expr) :=
  Expr.app (Expr.app op l) r

def toACExpr (op l r : Expr) : MetaM (Array Expr × ACExpr) := do
  let (preExpr, vars) ←
    toPreExpr (mkApp2 op l r)
    |>.run HashSet.empty
  let vars := vars.toArray.insertionSort Expr.lt
  let varMap := vars.foldl (fun xs x => xs.insert x xs.size) HashMap.empty |>.find!

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

  let α ← inferType vars[0]!
  let u ← getLevel α
  let (isNeutrals, context) ← mkContext α u vars
  let acExprNormed := Data.AC.evalList ACExpr preContext $ Data.AC.norm (preContext, isNeutrals) acExpr
  let tgt := convertTarget vars acExprNormed
  let lhs := convert acExpr
  let rhs := convert acExprNormed
  let proof := mkAppN (mkConst ``Context.eq_of_norm [u]) #[α, context, lhs, rhs, ←mkEqRefl (mkConst ``Bool.true)]
  return (proof, tgt)
where
  mkContext (α : Expr) (u : Level) (vars : Array Expr) : MetaM (Array Bool × Expr) := do
    let arbitrary := vars[0]!
    let zero := mkLevelZeroEx ()
    let noneE := mkApp (mkConst ``Option.none [zero])
    let someE := mkApp2 (mkConst ``Option.some [zero])

    let vars ← vars.mapM fun x => do
      let isNeutral :=
        let isNeutralClass := mkApp3 (mkConst ``IsNeutral [u]) α preContext.op x
        match ←getInstance ``IsNeutral #[preContext.op, x] with
        | none => (false, noneE isNeutralClass)
        | some isNeutral => (true, someE isNeutralClass isNeutral)

      return (isNeutral.1, mkApp4 (mkConst ``Variable.mk [u]) α preContext.op x isNeutral.2)

    let (isNeutrals, vars) := vars.unzip
    let vars := vars.toList
    let vars ← mkListLit (mkApp2 (mkConst ``Variable [u]) α preContext.op) vars

    let comm :=
      let commClass := mkApp2 (mkConst ``IsCommutative [u]) α preContext.op
      match preContext.comm with
      | none => noneE commClass
      | some comm => someE commClass comm

    let idem :=
      let idemClass := mkApp2 (mkConst ``IsIdempotent [u]) α preContext.op
      match preContext.idem with
      | none => noneE idemClass
      | some idem => someE idemClass idem

    return (isNeutrals, mkApp7 (mkConst ``Lean.Data.AC.Context.mk [u]) α preContext.op preContext.assoc comm idem vars arbitrary)

  convert : ACExpr → Expr
    | Data.AC.Expr.op l r => mkApp2 (mkConst ``Data.AC.Expr.op) (convert l) (convert r)
    | Data.AC.Expr.var x => mkApp (mkConst ``Data.AC.Expr.var) $ mkNatLit x

  convertTarget (vars : Array Expr) : ACExpr → Expr
    | Data.AC.Expr.op l r => mkApp2 preContext.op (convertTarget vars l) (convertTarget vars r)
    | Data.AC.Expr.var x => vars[x]!

def rewriteUnnormalized (mvarId : MVarId) : MetaM Unit := do
  let simpCtx :=
    {
      simpTheorems  := {}
      congrTheorems := (← getSimpCongrTheorems)
      config        := Simp.neutralConfig
    }
  let tgt ← instantiateMVars (← mvarId.getType)
  let (res, _) ← Simp.main tgt simpCtx (methods := { post })
  let newGoal ← applySimpResultToTarget mvarId tgt res
  newGoal.refl
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

@[builtin_tactic acRfl] def acRflTactic : Lean.Elab.Tactic.Tactic := fun _ => do
  let goal ← getMainGoal
  goal.withContext <| rewriteUnnormalized goal

builtin_initialize
  registerTraceClass `Meta.AC

end Lean.Meta.AC
