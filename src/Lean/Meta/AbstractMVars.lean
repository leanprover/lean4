/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic

namespace Lean
namespace Meta

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
s ← get;
let fresh := s.ngen.curr;
modify $ fun s => { s with ngen := s.ngen.next };
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
| u@(Level.succ v _)      => do v ← visitLevel abstractLevelMVars v; pure $ u.updateSucc v rfl
| u@(Level.max v w _)     => do v ← visitLevel abstractLevelMVars v; w ← visitLevel abstractLevelMVars w; pure $ u.updateMax v w rfl
| u@(Level.imax v w _)    => do v ← visitLevel abstractLevelMVars v; w ← visitLevel abstractLevelMVars w; pure $ u.updateIMax v w rfl
| u@(Level.mvar mvarId _) => do
  mctx ← read;
  let depth := mctx.getLevelDepth mvarId;
  if depth != mctx.depth then pure u -- metavariables from lower depths are treated as constants
  else do
    s ← get;
    match s.lmap.find? mvarId with
    | some u => pure u
    | none   => do
      let paramId := mkNameNum `_abstMVar s.nextParamIdx;
      let u := mkLevelParam paramId;
      modify $ fun s => { s with nextParamIdx := s.nextParamIdx + 1, lmap := s.lmap.insert mvarId u, paramNames := s.paramNames.push paramId };
      pure u

partial def abstractExprMVars : Expr → M Expr
| e@(Expr.lit _ _)         => pure e
| e@(Expr.bvar _ _)        => pure e
| e@(Expr.fvar _ _)        => pure e
| e@(Expr.sort u _)        => do u ← visitLevel abstractLevelMVars u; pure $ e.updateSort u rfl
| e@(Expr.const _ us _)    => do us ← us.mapM (visitLevel abstractLevelMVars); pure $ e.updateConst us rfl
| e@(Expr.proj _ _ s _)    => do s ← visitExpr abstractExprMVars s; pure $ e.updateProj s rfl
| e@(Expr.app f a _)       => do f ← visitExpr abstractExprMVars f; a ← visitExpr abstractExprMVars a; pure $ e.updateApp f a rfl
| e@(Expr.mdata _ b _)     => do b ← visitExpr abstractExprMVars b; pure $ e.updateMData b rfl
| e@(Expr.lam _ d b _)     => do d ← visitExpr abstractExprMVars d; b ← visitExpr abstractExprMVars b; pure $ e.updateLambdaE! d b
| e@(Expr.forallE _ d b _) => do d ← visitExpr abstractExprMVars d; b ← visitExpr abstractExprMVars b; pure $ e.updateForallE! d b
| e@(Expr.letE _ t v b _)  => do t ← visitExpr abstractExprMVars t; v ← visitExpr abstractExprMVars v; b ← visitExpr abstractExprMVars b; pure $ e.updateLet t v b rfl
| e@(Expr.mvar mvarId _)   => do
  mctx ← read;
  let decl := mctx.getDecl mvarId;
  if decl.depth != mctx.depth then pure e -- metavariables from lower depths are treated as constants
  else do
    s ← get;
    match s.emap.find? mvarId with
    | some e => pure e
    | none   => do
      type   ← visitExpr abstractExprMVars decl.type;
      fvarId ← mkFreshId;
      let fvar := mkFVar fvarId;
      let userName := if decl.userName.isAnonymous then (`x).appendIndexAfter s.fvars.size else decl.userName;
      modify $ fun s => {
        s with
        emap  := s.emap.insert mvarId fvar,
        fvars := s.fvars.push fvar,
        lctx  := s.lctx.mkLocalDecl fvarId userName type };
      pure fvar
| Expr.localE _ _ _ _    => unreachable!

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
e ← instantiateMVars e;
ngen ← getNGen;
lctx ← getLCtx;
mctx ← getMCtx;
let (e, s) := AbstractMVars.abstractExprMVars e mctx { lctx := lctx, ngen := ngen };
setNGen s.ngen;
let e := s.lctx.mkLambda s.fvars e;
pure { paramNames := s.paramNames, numMVars := s.fvars.size, expr := e }

def openAbstractMVarsResult (a : AbstractMVarsResult) : MetaM (Array Expr × Array BinderInfo × Expr) := do
us ← a.paramNames.mapM $ fun _ => mkFreshLevelMVar;
let e := a.expr.instantiateLevelParamsArray a.paramNames us;
lambdaMetaTelescope e (some a.numMVars)

end Meta
end Lean
