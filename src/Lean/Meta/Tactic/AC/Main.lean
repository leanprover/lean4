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
open Lean.Data.AC.Expr

structure PreContext where
  id : Nat
  op : Expr
  assoc : Expr
  comm : Option Expr
  idem : Option Expr
  deriving Inhabited

instance : ContextInformation (Std.HashMap Nat (Option Expr) × PreContext) where
  isComm ctx := ctx.2.comm.isSome
  isIdem ctx := ctx.2.idem.isSome
  isNeutral ctx x := ctx.1.find? x |>.bind id |>.isSome

instance : EvalInformation PreContext ACExpr where
  arbitrary _ := var 0
  evalOp _ := op
  evalVar _ x := var x

structure ACNormContext where
  preContexts : ExprMap (Option PreContext)
  preContextsReverse : Array PreContext
  exprIds : ExprMap Nat
  exprIdsReverse : Array Expr
  neutrals : Std.HashMap (Nat × Nat) (Option Lean.Expr)

def emptyACNormContext : ACNormContext :=
  { preContexts := Std.HashMap.empty,
    exprIds := Std.HashMap.empty,
    exprIdsReverse := #[]
    preContextsReverse := #[],
    neutrals := Std.HashMap.empty }

abbrev M α := StateT ACNormContext MetaM α

def lazyCache
  (lookup : ACNormContext → α → Option β)
  (insert : ACNormContext → α → β → ACNormContext)
  (create : ACNormContext → α → MetaM β)
  (a : α) : M β := do
  let state ← get
  if let some b := lookup state a then
    return b
  else
    let b ← create state a
    set $ insert state a b
    return b

def getInstance (cls : Name) (exprs : Array Expr) : MetaM (Option Expr) := do
  try
    let app ← mkAppM cls exprs
    trace[Meta.AC] "trying: {indentExpr app}"
    let inst ← synthInstance app
    trace[Meta.AC] "got instance"
    return some inst
  catch
  | _ => return none

def preContextCache : Expr → M (Option PreContext) :=
  lazyCache
    (fun ctx => ctx.preContexts.find?)
    (fun ctx a b => { ctx with
      preContexts := ctx.preContexts.insert a b,
      preContextsReverse := if let some b := b then ctx.preContextsReverse.push b else ctx.preContextsReverse })
    fun ctx expr => do
    if let some assoc := ←getInstance ``IsAssociative #[expr] then
      return some
        { assoc,
          op := expr
          id := ctx.preContextsReverse.size
          comm := ←getInstance ``IsCommutative #[expr]
          idem := ←getInstance ``IsIdempotent #[expr] }

    return none

def exprId : Expr → M Nat :=
  lazyCache
    (fun ctx => ctx.exprIds.find?)
    (fun ctx a b => { ctx with exprIds := ctx.exprIds.insert a b, exprIdsReverse := ctx.exprIdsReverse.push a})
    fun ctx expr => pure ctx.exprIdsReverse.size

def neutralCache (op : Nat) (var : Nat) : M (Option Expr) :=
  lazyCache
    (fun ctx => ctx.neutrals.find?)
    (fun ctx a b => { ctx with neutrals := ctx.neutrals.insert a b })
    (fun ctx (op, var) => do
      let op := ctx.preContextsReverse[op].op
      let var := ctx.exprIdsReverse[var]
      getInstance ``IsNeutral #[op, var])
    (op, var)

inductive NormalizedExpr
| maybeNormalized (opId : Nat) (l : NormalizedExpr) (r : NormalizedExpr)
| definitelyNormalized (varId : Nat)
| unnormalized (opId : Nat) (e : NormalizedExpr)
  deriving Inhabited, Repr

open NormalizedExpr

def NormalizedExpr.norm : NormalizedExpr → M NormalizedExpr
  | definitelyNormalized id => pure $ definitelyNormalized id
  | e@(maybeNormalized opId _ _) => normalize opId e
  | e@(unnormalized opId _) => normalize opId e
where
  loop (opId : Nat) : NormalizedExpr → StateT (Std.HashMap Nat (Option Expr)) M ACExpr
      | definitelyNormalized x => do
        let isNeutral ← neutralCache opId x
        modify fun state => state.insert x isNeutral
        return var x
      | unnormalized _ e => loop opId e
      | maybeNormalized _ l r => return op (←loop opId l) (←loop opId r)

  normalize (opId : Nat) (e : NormalizedExpr) := do
    let (orig, neutrals) ← loop opId e |>.run Std.HashMap.empty
    let preContext := (←get).preContextsReverse[opId]
    return convertBack opId $ evalList ACExpr preContext $ Lean.Data.AC.norm (neutrals, preContext) orig

  convertBack (opId : Nat) : ACExpr → NormalizedExpr
    | var id => definitelyNormalized id
    | op l r => maybeNormalized opId (convertBack opId l) (convertBack opId r)

def NormalizedExpr.decide : NormalizedExpr → M (Option (Nat × NormalizedExpr))
  | definitelyNormalized _ => pure none
  | unnormalized opId e => pure (opId, e)
  | e@(maybeNormalized opId l r) => do
    let rec loop : NormalizedExpr → StateT (Std.HashMap Nat (Option Expr)) M ACExpr
      | definitelyNormalized x => do
        let isNeutral ← neutralCache opId x
        modify fun state => state.insert x isNeutral
        return var x
      | unnormalized _ e => loop e
      | maybeNormalized _ l r => return op (←loop l) (←loop r)

    let (orig, neutrals) ← loop e |>.run Std.HashMap.empty
    let preContext := (←get).preContextsReverse[opId]
    let res := evalList ACExpr preContext $ Lean.Data.AC.norm (neutrals, preContext) orig

    return if orig == res then none else some (opId, e)

open Lean.Expr

@[matchPattern] def bin {x₁ x₂} (op l r : Expr) :=
  app (app op l x₁) r x₂

@[matchPattern] def eq {eq₁ eq₂ eq₃ eq₄ app₁ app₂ n₁} (l r : Expr) :=
  app (app (app (const (Lean.Name.str Lean.Name.anonymous "Eq" n₁) eq₁ eq₂) eq₃ eq₄) l app₁) r app₂

partial def findUnnormalizedOperator (e : Expr) : M NormalizedExpr := do
  match e with
  | lam _ dom b _ => decide [dom, b] >>= wrap
  | forallE _ dom b _ => decide [dom, b] >>= wrap
  | letE _ ty val b _ => decide [ty, val, b] >>= wrap
  | mdata _ e _ => findUnnormalizedOperator e
  | proj _ _ e _ => decide [e] >>= wrap
  | bin opExpr lExpr rExpr => do
    match ←preContextCache opExpr with
    | none => decide [lExpr, rExpr] >>= wrap
    | some pc =>
      match ←matchWithOp pc.id lExpr with
      | (false, l) => return l
      | (true, l) =>
        match ←matchWithOp pc.id rExpr with
        | (false, r) => return r
        | (true, r) => return maybeNormalized pc.id l r

  | app f a _ => decide [f, a] >>= wrap
  | atom =>
    return definitelyNormalized (←exprId atom)
  where
    decide : List Lean.Expr → M (Option (Nat × NormalizedExpr))
    | [] => pure none
    | x :: xs => do
      match ←findUnnormalizedOperator x with
      | definitelyNormalized _ => decide xs
      | unnormalized opId e => pure $ some (opId, e)
      | e@(maybeNormalized _ _ _) => return (←e.decide) <|> (←decide xs)

    wrap : Option (Nat × NormalizedExpr) → M NormalizedExpr
    | none => return definitelyNormalized (←exprId e)
    | some (opId, e) => return unnormalized opId e

    matchWithOp (op : Nat) (expr : Lean.Expr) : M (Bool × NormalizedExpr) := do
      match ←findUnnormalizedOperator expr with
      | e@(unnormalized _ _) => return (false, e)
      | e@(definitelyNormalized _) =>
        return (true, e)
      | e@(maybeNormalized op₂ _ _) =>
        match op == op₂ with
        | true => return (true, e)
        | false =>
          match ←e.decide with
          | none => return (true, definitelyNormalized (←exprId expr))
          | some (op, e) => return (false, unnormalized op e)

def buildProof (lhs rhs : NormalizedExpr) : M (Lean.Expr × Lean.Expr) := do
  let vars :=
    getVars (maybeNormalized 0 lhs rhs)
    |>.run Std.HashSet.empty
    |>.2.toArray.insertionSort Nat.ble

  let varMap := vars.foldl (fun xs x => xs.insert x xs.size) Std.HashMap.empty |>.find!

  let (preContext, context) ← mkContext vars
  let ty ← mkEq (←convertType preContext.op lhs) (←convertType preContext.op rhs) let lhs ← convert varMap lhs
  let rhs ← convert varMap rhs
  let proof ← mkAppM ``Context.eq_of_norm #[context, lhs, rhs, ←mkEqRefl $ ←mkAppM ``Lean.Data.AC.norm #[context, lhs]]
  return (proof, ty)
where
  getVars : NormalizedExpr → StateM (Std.HashSet Nat) Unit
    | definitelyNormalized x => modify fun xs => xs.insert x
    | unnormalized opId e => getVars e
    | maybeNormalized opId l r => do getVars l; getVars r

  mkContext (vars : Array Nat) : M (PreContext × Lean.Expr) := do
    let op :=
      match lhs, rhs with
      | definitelyNormalized _, definitelyNormalized _ => 0
      | unnormalized opId _, _ => opId
      | maybeNormalized opId _ _, _ => opId
      | _, unnormalized opId _ => opId
      | _, maybeNormalized opId _ _ => opId

    let ctx ← get
    let arbitrary := ctx.exprIdsReverse[vars[0]]
    let preContext := ctx.preContextsReverse[op]
    let vars : List Lean.Expr ← vars.toList.mapM fun x => do
      let xExpr := ctx.exprIdsReverse[x]
      let isNeutral ←
        match ←neutralCache op x with
        | none => mkAppOptM ``Option.none #[←mkAppM ``IsNeutral #[preContext.op, xExpr]]
        | some isNeutral => mkAppM ``Option.some #[isNeutral]

      mkAppM ``Variable.mk #[xExpr, isNeutral]

    let vars ← Lean.Meta.mkListLit (←mkAppM ``Variable #[preContext.op]) vars

    let comm ←
      match preContext.comm with
      | none => mkAppOptM ``Option.none #[←mkAppM ``IsCommutative #[preContext.op]]
      | some comm => mkAppM ``Option.some #[comm]

    let idem ←
      match preContext.idem with
      | none => mkAppOptM ``Option.none #[←mkAppM ``IsIdempotent #[preContext.op]]
      | some idem => mkAppM ``Option.some #[idem]
    return (preContext, ←mkAppM ``Lean.Data.AC.Context.mk #[preContext.op, preContext.assoc, comm, idem, vars, arbitrary])

  convert (varMap : Nat → Nat) : NormalizedExpr → MetaM Lean.Expr
    | definitelyNormalized id => mkAppM ``var #[Lean.mkNatLit $ varMap id]
    | unnormalized _ e => convert varMap e
    | maybeNormalized _ l r => do mkAppM ``op #[←convert varMap l, ←convert varMap r]

  convertType (op : Lean.Expr) : NormalizedExpr → M Lean.Expr
    | definitelyNormalized id => do return (←get).exprIdsReverse[id]
    | unnormalized _ e => convertType op e
    | maybeNormalized _ l r => do mkAppM' op #[←convertType op l, ←convertType op r]

inductive ProofStrategy
  | rfl (lhs rhs : NormalizedExpr)
  | norm (e : NormalizedExpr)

def pickStrategy (e : Expr) : M ProofStrategy := do
  match e with
  | eq lhs rhs =>
    match ←findUnnormalizedOperator lhs with
    | lhs@(unnormalized _ _) => return ProofStrategy.norm lhs
    | lhs =>
      match ←findUnnormalizedOperator rhs with
      | rhs@(unnormalized _ _) => return ProofStrategy.norm rhs
      | rhs => return ProofStrategy.rfl lhs rhs
  | e => return ProofStrategy.norm $ ←findUnnormalizedOperator e

def addAcEq (mvarId : MVarId) (e : NormalizedExpr) (target : Expr) : M MVarId := do
  let (proof, ty) ← buildProof e (←e.norm)
  let goal ← withLocalDeclD `h_ac ty fun h_ac =>
    mkForallFVars #[h_ac] target
  let goal ← mkFreshExprMVar goal
  assignExprMVar mvarId (mkApp goal proof)
  return goal.mvarId!

partial def rewriteUnnormalized (mvarId : MVarId) : M Unit :=
  withMVarContext mvarId do
  let target ← getMVarType mvarId
  match ←pickStrategy target with
  | ProofStrategy.rfl lhs rhs =>
    trace[Meta.AC] "picking rfl strategy {MessageData.ofGoal mvarId}"
    try
      let (proof, ty) ← buildProof lhs rhs
      if ←isDefEq target ty then
        assignExprMVar mvarId proof
      else throwError ""
    catch _ => throwError "cannot synthesize proof:\n{MessageData.ofGoal mvarId}"
  | ProofStrategy.norm (definitelyNormalized _) => throwError "no unnormalized operators found"
  | ProofStrategy.norm e =>
    trace[Meta.AC] "picking norm strategy {MessageData.ofGoal mvarId}"
    let mvarId ← addAcEq mvarId e target
    let (h_ac, mvarId) ← intro mvarId `h_ac
    let res ← rewrite mvarId (←getMVarType mvarId) (mkFVar h_ac)
    let [] := res.mvarIds | throwError "no meta variables expected after rewrite"
    let mvarId ← replaceTargetEq mvarId res.eNew res.eqProof
    let mvarId ← clear mvarId h_ac
    rewriteUnnormalized mvarId

syntax (name := ac_refl) "ac_refl " : tactic
@[builtinTactic ac_refl] def ac_refl_tactic : Lean.Elab.Tactic.Tactic := fun stx => do
  let goal ← getMainGoal
  (rewriteUnnormalized goal).run' emptyACNormContext

builtin_initialize
  registerTraceClass `Meta.AC

end Lean.Meta.AC
