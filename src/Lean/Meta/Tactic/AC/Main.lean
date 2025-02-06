/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
prelude
import Init.Data.AC
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Simp.Main
import Lean.Elab.Tactic.Rewrite

namespace Lean.Meta.AC
open Lean.Data.AC
open Lean.Elab.Tactic
open Std

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
  if let some assoc := ←getInstance ``Associative #[expr] then
    return some
      { assoc,
        op := expr
        id := 0
        comm := ←getInstance ``Commutative #[expr]
        idem := ←getInstance ``IdempotentOp #[expr] }

  return none

inductive PreExpr
| op (lhs rhs : PreExpr)
| var (e : Expr)

@[match_pattern] def bin (op l r : Expr) :=
  Expr.app (Expr.app op l) r

def toACExpr (op l r : Expr) : MetaM (Array Expr × ACExpr) := do
  let (preExpr, vars) ←
    toPreExpr (mkApp2 op l r)
    |>.run Std.HashSet.empty
  let vars := vars.toArray.insertionSort Expr.lt
  let varMap := vars.foldl (fun xs x => xs.insert x xs.size) Std.HashMap.empty |>.get!

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

/--
In order to prevent the kernel trying to reduce the atoms of the expression, we abstract the proof
over them. But `ac_rfl` proofs are not completely abstract in the value of the atoms – it recognizes
neutral elements. So we have to abstract over these proofs as well.
-/
def abstractAtoms (preContext : PreContext) (atoms : Array Expr)
    (k : Array (Expr × Option Expr) → MetaM Expr) : MetaM Expr := do
  let α ← inferType atoms[0]!
  let u ← getLevel α
  let rec go i (acc : Array (Expr × Option Expr)) (vars : Array Expr) (args : Array Expr) := do
    if h : i < atoms.size then
      withLocalDeclD `x α fun v => do
        match (← getInstance ``LawfulIdentity #[preContext.op, atoms[i]]) with
        | none =>
          go (i+1) (acc.push (v, .none)) (vars.push v) (args.push atoms[i])
        | some inst =>
          withLocalDeclD `inst (mkApp3 (mkConst ``LawfulIdentity [u]) α preContext.op v) fun iv =>
            go (i+1) (acc.push (v, .some iv)) (vars ++ #[v,iv]) (args ++ #[atoms[i], inst])
    else
      let proof ← k acc
      let proof ← mkLambdaFVars vars proof
      let proof := mkAppN proof args
      return proof
  go 0 #[] #[] #[]

def buildNormProof (preContext : PreContext) (l r : Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let (atoms, acExpr) ← toACExpr preContext.op l r
  let proof ← abstractAtoms preContext atoms fun varsData => do
    let α ← inferType atoms[0]!
    let u ← getLevel α
    let context ← mkContext α u varsData
    let isNeutrals := varsData.map (·.2.isSome)
    let vars := varsData.map (·.1)
    let acExprNormed := Data.AC.evalList ACExpr preContext $ Data.AC.norm (preContext, isNeutrals) acExpr
    let lhs := convert acExpr
    let rhs := convert acExprNormed
    let proof := mkAppN (mkConst ``Context.eq_of_norm [u]) #[α, context, lhs, rhs, ←mkEqRefl (mkConst ``Bool.true)]
    let proofType ← mkEq (convertTarget vars acExpr) (convertTarget vars acExprNormed)
    let proof ← mkExpectedTypeHint proof proofType
    return proof
  let some (_, _, tgt) := (← inferType proof).eq? | panic! "unexpected proof type"
  return (proof, tgt)
where
  mkContext (α : Expr) (u : Level) (vars : Array (Expr × Option Expr)) : MetaM Expr := do
    let arbitrary := vars[0]!.1
    let plift := mkApp (mkConst ``PLift [.zero])
    let pliftUp := mkApp2 (mkConst ``PLift.up [.zero])
    let noneE tp   := mkApp  (mkConst ``Option.none [.zero]) (plift tp)
    let someE tp v := mkApp2 (mkConst ``Option.some [.zero]) (plift tp) (pliftUp tp v)
    let vars ← vars.mapM fun ⟨x, inst?⟩ =>
      let isNeutral :=
        let isNeutralClass := mkApp3 (mkConst ``LawfulIdentity [u]) α preContext.op x
        match inst? with
        | none => noneE isNeutralClass
        | some isNeutral => someE isNeutralClass isNeutral
      return mkApp4 (mkConst ``Variable.mk [u]) α preContext.op x isNeutral

    let vars := vars.toList
    let vars ← mkListLit (mkApp2 (mkConst ``Variable [u]) α preContext.op) vars

    let comm :=
      let commClass := mkApp2 (mkConst ``Commutative [u]) α preContext.op
      match preContext.comm with
      | none => noneE commClass
      | some comm => someE commClass comm

    let idem :=
      let idemClass := mkApp2 (mkConst ``IdempotentOp [u]) α preContext.op
      match preContext.idem with
      | none => noneE idemClass
      | some idem => someE idemClass idem

    return mkApp7 (mkConst ``Lean.Data.AC.Context.mk [u]) α preContext.op preContext.assoc comm idem vars arbitrary

  convert : ACExpr → Expr
    | .op l r => mkApp2 (mkConst ``Data.AC.Expr.op) (convert l) (convert r)
    | .var x => mkApp (mkConst ``Data.AC.Expr.var) $ mkNatLit x

  convertTarget (vars : Array Expr) : ACExpr → Expr
    | .op l r => mkApp2 preContext.op (convertTarget vars l) (convertTarget vars r)
    | .var x => vars[x]!

def post (e : Expr) : SimpM Simp.Step := do
  let ctx ← Simp.getContext
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

def rewriteUnnormalized (mvarId : MVarId) : MetaM MVarId := do
  let simpCtx ← Simp.mkContext
      (simpTheorems  := {})
      (congrTheorems := (← getSimpCongrTheorems))
      (config        := Simp.neutralConfig)
  let tgt ← instantiateMVars (← mvarId.getType)
  let (res, _) ← Simp.main tgt simpCtx (methods := { post })
  applySimpResultToTarget mvarId tgt res

def rewriteUnnormalizedRefl (goal : MVarId) : MetaM Unit := do
  (← rewriteUnnormalized goal).refl

@[builtin_tactic acRfl] def acRflTactic : Lean.Elab.Tactic.Tactic := fun _ => do
  let goal ← getMainGoal
  goal.withContext <| rewriteUnnormalizedRefl goal

def acNfHypMeta (goal : MVarId) (fvarId : FVarId) : MetaM (Option MVarId) := do
  goal.withContext do
    let simpCtx ← Simp.mkContext
      (simpTheorems  := {})
      (congrTheorems := (← getSimpCongrTheorems))
      (config        := Simp.neutralConfig)
    let tgt ← instantiateMVars (← fvarId.getType)
    let (res, _) ← Simp.main tgt simpCtx (methods := { post })
    return (← applySimpResultToLocalDecl goal fvarId res false).map (·.snd)

/-- Implementation of the `ac_nf` tactic when operating on the main goal. -/
def acNfTargetTactic : TacticM Unit :=
  liftMetaTactic1 fun goal => rewriteUnnormalized goal

/-- Implementation of the `ac_nf` tactic when operating on a hypothesis. -/
def acNfHypTactic (fvarId : FVarId) : TacticM Unit :=
  liftMetaTactic1 fun goal => acNfHypMeta goal fvarId

@[builtin_tactic acNf0]
def evalNf0 : Tactic := fun stx => do
  match stx with
  | `(tactic| ac_nf0 $[$loc?]?) =>
    let loc := if let some loc := loc? then expandLocation loc else Location.targets #[] true
    withMainContext do
      match loc with
      | Location.targets hyps target =>
        if target then acNfTargetTactic
        (← getFVarIds hyps).forM acNfHypTactic
      | Location.wildcard =>
        acNfTargetTactic
        (← (← getMainGoal).getNondepPropHyps).forM acNfHypTactic
  | _ => Lean.Elab.throwUnsupportedSyntax

builtin_initialize
  registerTraceClass `Meta.AC

end Lean.Meta.AC
