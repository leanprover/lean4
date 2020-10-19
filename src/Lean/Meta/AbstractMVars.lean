#lang lean4
/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic

namespace Lean.Meta

structure AbstractMVarsResult :=
(paramNames : Array Name)
(numMVars   : Nat)
(expr       : Expr)

instance AbstractMVarsResult.inhabited : Inhabited AbstractMVarsResult := ⟨⟨#[], 0, arbitrary _⟩⟩

def AbstractMVarsResult.beq (r₁ r₂ : AbstractMVarsResult) : Bool :=
r₁.paramNames == r₂.paramNames && r₁.numMVars == r₂.numMVars && r₁.expr == r₂.expr

instance AbstractMVarsResult.hasBeq : HasBeq AbstractMVarsResult := ⟨AbstractMVarsResult.beq⟩

namespace AbstractMVars

open Std (HashMap)

structure State :=
(ngen         : NameGenerator)
(lctx         : LocalContext)
(nextParamIdx : Nat := 0)
(paramNames   : Array Name := #[])
(fvars        : Array Expr  := #[])
(lmap         : HashMap Name Level := {})
(emap         : HashMap Name Expr  := {})

abbrev M := ReaderT MetavarContext (StateM State)

def mkFreshId : M Name := do
let s ← get
let fresh := s.ngen.curr
modify fun s => { s with ngen := s.ngen.next }
pure fresh

@[inline] private def visitLevel (f : Level → M Level) (u : Level) : M Level :=
if !u.hasMVar then pure u
else f u

@[inline] private def visitExpr (f : Expr → M Expr) (e : Expr) : M Expr :=
if !e.hasMVar then pure e
else f e

private partial def abstractLevelMVars : Level → M Level
| u@(Level.zero _)        => pure u
| u@(Level.param _ _)     => pure u
| u@(Level.succ v _)      => do return u.updateSucc! (← visitLevel abstractLevelMVars v)
| u@(Level.max v w _)     => do return u.updateMax! (← visitLevel abstractLevelMVars v) (← visitLevel abstractLevelMVars w)
| u@(Level.imax v w _)    => do return u.updateIMax! (← visitLevel abstractLevelMVars v) (← visitLevel abstractLevelMVars w)
| u@(Level.mvar mvarId _) => do
  let mctx ← read
  let depth := mctx.getLevelDepth mvarId;
  if depth != mctx.depth then pure u -- metavariables from lower depths are treated as constants
  else
    let s ← get
    match s.lmap.find? mvarId with
    | some u => pure u
    | none   =>
      let paramId := mkNameNum `_abstMVar s.nextParamIdx
      let u := mkLevelParam paramId
      modify fun s => { s with nextParamIdx := s.nextParamIdx + 1, lmap := s.lmap.insert mvarId u, paramNames := s.paramNames.push paramId }
      pure u

partial def abstractExprMVars : Expr → M Expr
| e@(Expr.lit _ _)         => pure e
| e@(Expr.bvar _ _)        => pure e
| e@(Expr.fvar _ _)        => pure e
| e@(Expr.sort u _)        => do return e.updateSort! (← visitLevel abstractLevelMVars u)
| e@(Expr.const _ us _)    => do return e.updateConst! (← us.mapM (visitLevel abstractLevelMVars))
| e@(Expr.proj _ _ s _)    => do return e.updateProj! (← visitExpr abstractExprMVars s)
| e@(Expr.app f a _)       => do return e.updateApp! (← visitExpr abstractExprMVars f) (← visitExpr abstractExprMVars a)
| e@(Expr.mdata _ b _)     => do return e.updateMData! (← visitExpr abstractExprMVars b)
| e@(Expr.lam _ d b _)     => do return e.updateLambdaE! (← visitExpr abstractExprMVars d) (← visitExpr abstractExprMVars b)
| e@(Expr.forallE _ d b _) => do return e.updateForallE! (← visitExpr abstractExprMVars d) (← visitExpr abstractExprMVars b)
| e@(Expr.letE _ t v b _)  => do return e.updateLet! (← visitExpr abstractExprMVars t) (← visitExpr abstractExprMVars v) (← visitExpr abstractExprMVars b)
| e@(Expr.mvar mvarId _)   => do
  let mctx ← read
  let decl := mctx.getDecl mvarId
  if decl.depth != mctx.depth then
    pure e -- metavariables from lower depths are treated as constants
  else
    let s ← get
    match s.emap.find? mvarId with
    | some e => pure e
    | none   =>
      let type   ← visitExpr abstractExprMVars decl.type
      let fvarId ← mkFreshId
      let fvar := mkFVar fvarId;
      let userName := if decl.userName.isAnonymous then (`x).appendIndexAfter s.fvars.size else decl.userName
      modify fun s => {
        s with
        emap  := s.emap.insert mvarId fvar,
        fvars := s.fvars.push fvar,
        lctx  := s.lctx.mkLocalDecl fvarId userName type }
      pure fvar
| Expr.localE .. => unreachable!

end AbstractMVars

/--
  Abstract (current depth) metavariables occurring in `e`.
  The result contains
  - An array of universe level parameters that replaced universe metavariables occurring in `e`.
  - The number of (expr) metavariables abstracted.
  - And an expression of the form `fun (m_1 : A_1) ... (m_k : A_k) => e'`, where
    `k` equal to the number of (expr) metavariables abstracted, and `e'` is `e` after we
    replace the metavariables.

  Example: given `f.{?u} ?m1` where `?m1 : ?m2 Nat`, `?m2 : Type -> Type`. This function returns
  `{ levels := #[u], size := 2, expr := (fun (m2 : Type -> Type) (m1 : m2 Nat) => f.{u} m1) }`

  This API can be used to "transport" to a different metavariable context.
  Given a new metavariable context, we replace the `AbstractMVarsResult.levels` with
  new fresh universe metavariables, and instantiate the `(m_i : A_i)` in the lambda-expression
  with new fresh metavariables.

  Application: we use this method to cache the results of type class resolution. -/
def abstractMVars (e : Expr) : MetaM AbstractMVarsResult := do
let e ← instantiateMVars e
let (e, s) := AbstractMVars.abstractExprMVars e (← getMCtx) { lctx := (← getLCtx), ngen := (← getNGen) }
setNGen s.ngen
let e := s.lctx.mkLambda s.fvars e
pure { paramNames := s.paramNames, numMVars := s.fvars.size, expr := e }

def openAbstractMVarsResult (a : AbstractMVarsResult) : MetaM (Array Expr × Array BinderInfo × Expr) := do
let us ← a.paramNames.mapM fun _ => mkFreshLevelMVar
let e := a.expr.instantiateLevelParamsArray a.paramNames us
lambdaMetaTelescope e (some a.numMVars)

end Lean.Meta
