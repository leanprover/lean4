/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.ShareCommon
import Lean.MetavarContext
import Lean.Environment
import Lean.Util.FoldConsts

namespace Lean
namespace Closure

structure Context :=
(lctxInput : LocalContext)
(zeta      : Bool) -- if `true` let-variables are expanded

structure State :=
(mctx          : MetavarContext)
(lctxOutput    : LocalContext := {})
(ngen          : NameGenerator := { namePrefix := `_closure })
(visitedLevel  : LevelMap Level := {})
(visitedExpr   : ExprStructMap Expr := {})
(levelParams   : Array Name := #[])
(nextLevelIdx  : Nat := 1)
(levelClosure  : Array Level := #[])
(nextExprIdx   : Nat := 1)
(exprClosure   : Array Expr := #[])

def Exception := String

abbrev ClosureM := ReaderT Context (EStateM Exception State)

@[inline] def visitLevel (f : Level → ClosureM Level) (u : Level) : ClosureM Level :=
if !u.hasMVar && !u.hasParam then pure u
else do
  s ← get;
  match s.visitedLevel.find? u with
  | some v => pure v
  | none   => do
    v ← f u;
    modify $ fun s => { s with visitedLevel := s.visitedLevel.insert u v };
    pure v

def mkNewLevelParam (u : Level) : ClosureM Level := do
s ← get;
let p := (`u).appendIndexAfter s.nextLevelIdx;
modify $ fun s => { s with levelParams := s.levelParams.push p, nextLevelIdx := s.nextLevelIdx + 1, levelClosure := s.levelClosure.push u };
pure $ mkLevelParam p

def getMCtx : ClosureM MetavarContext := do
s ← get; pure s.mctx

def instantiateMVars (e : Expr) : ClosureM Expr := do
modifyGet fun s =>
  let (e, mctx) := s.mctx.instantiateMVars e;
  (e, { s with mctx := mctx })

partial def collectLevelAux : Level → ClosureM Level
| u@(Level.succ v _)      => do v ← visitLevel collectLevelAux v; pure $ u.updateSucc! v
| u@(Level.max v w _)     => do v ← visitLevel collectLevelAux v; w ← visitLevel collectLevelAux w; pure $ u.updateMax! v w
| u@(Level.imax v w _)    => do v ← visitLevel collectLevelAux v; w ← visitLevel collectLevelAux w; pure $ u.updateIMax! v w
| u@(Level.mvar mvarId _) => mkNewLevelParam u
| u@(Level.param _ _)     => mkNewLevelParam u
| u@(Level.zero _)        => pure u

def collectLevel (u : Level) : ClosureM Level :=
visitLevel collectLevelAux u

instance : MonadNameGenerator ClosureM :=
{ getNGen := do s ← get; pure s.ngen,
  setNGen := fun ngen => modify fun s => { s with ngen := ngen } }

/--
  Remark: This method does not guarantee unique user names.
  The correctness of the procedure does not rely on unique user names.
  Recall that the pretty printer takes care of unintended collisions. -/
def mkNextUserName : ClosureM Name := do
s ← get;
let n := (`_x).appendIndexAfter s.nextExprIdx;
modify $ fun s => { s with nextExprIdx := s.nextExprIdx + 1 };
pure n

def getUserName (userName? : Option Name) : ClosureM Name :=
match userName? with
| some userName => pure userName
| none          => mkNextUserName

def mkLocalDecl (userName? : Option Name) (type : Expr) (bi : BinderInfo) : ClosureM Expr := do
userName ← getUserName userName?;
fvarId   ← mkFreshFVarId;
modify $ fun s => { s with lctxOutput := s.lctxOutput.mkLocalDecl fvarId userName type bi };
pure $ mkFVar fvarId

def mkLetDecl (userName : Name) (type : Expr) (value : Expr) (nonDep : Bool) : ClosureM Expr := do
fvarId   ← mkFreshFVarId;
modify $ fun s => { s with lctxOutput := s.lctxOutput.mkLetDecl fvarId userName type value nonDep };
pure $ mkFVar fvarId

@[inline] def visitExpr (f : Expr → ClosureM Expr) (e : Expr) : ClosureM Expr :=
if !e.hasLevelParam && !e.hasFVar && !e.hasMVar then pure e
else do
  s ← get;
  match s.visitedExpr.find? e with
  | some r => pure r
  | none   => do
    r ← f e;
    modify $ fun s => { s with visitedExpr := s.visitedExpr.insert e r };
    pure r

partial def collectExprAux : Expr → ClosureM Expr
| e =>
  let collect (e : Expr) := visitExpr collectExprAux e;
  match e with
  | Expr.proj _ _ s _    => do s ← collect s; pure (e.updateProj! s)
  | Expr.forallE _ d b _ => do d ← collect d; b ← collect b; pure (e.updateForallE! d b)
  | Expr.lam _ d b _     => do d ← collect d; b ← collect b; pure (e.updateLambdaE! d b)
  | Expr.letE _ t v b _  => do t ← collect t; v ← collect v; b ← collect b; pure (e.updateLet! t v b)
  | Expr.app f a _       => do f ← collect f; a ← collect a; pure (e.updateApp! f a)
  | Expr.mdata _ b _     => do b ← collect b; pure (e.updateMData! b)
  | Expr.sort u _        => do u ← collectLevel u; pure (e.updateSort! u)
  | Expr.const c us _    => do us ← us.mapM collectLevel; pure (e.updateConst! us)
  | Expr.mvar mvarId _   => do
    mctx ← getMCtx;
    match mctx.findDecl? mvarId with
    | none          => throw "unknown metavariable"
    | some mvarDecl => do
      type ← instantiateMVars mvarDecl.type;
      type ← collect type;
      x    ← mkLocalDecl none type BinderInfo.default;
      modify $ fun s => { s with exprClosure := s.exprClosure.push e };
      pure x
  | Expr.fvar fvarId _ => do
    ctx ← read;
    match ctx.lctxInput.find? fvarId with
    | none => throw "unknown free variable"
    | some (LocalDecl.cdecl _ _ userName type bi) => do
      type ← instantiateMVars type;
      type ← collect type;
      x    ← mkLocalDecl userName type bi;
      modify $ fun s => { s with exprClosure := s.exprClosure.push e };
      pure x
    | some (LocalDecl.ldecl _ _ userName type value nonDep) =>
      if ctx.zeta then do
        value ← instantiateMVars value;
        collect value
      else do
        type  ← instantiateMVars type;
        type  ← collect type;
        value ← instantiateMVars value;
        value ← collect value;
        -- Note that let-declarations do not need to be provided to the closure being constructed.
        mkLetDecl userName type value nonDep
  | e => pure e

def collectExpr (e : Expr) : ClosureM Expr := do
e ← instantiateMVars e;
visitExpr collectExprAux e

structure ExprToClose :=
(expr   : Expr)
(isType : Bool)

instance ExprToClose.inhabited : Inhabited ExprToClose := ⟨⟨arbitrary _, arbitrary _⟩⟩

structure MkClosureResult :=
(levelParams  : Array Name)
(exprs        : Array Expr)
(levelClosure : Array Level)
(exprClosure  : Array Expr)
(mctx         : MetavarContext)

def mkClosure (mctx : MetavarContext) (lctx : LocalContext) (exprsToClose : Array ExprToClose) (zeta : Bool := false) : Except String MkClosureResult :=
let shareCommonExprs : Std.ShareCommonM (Array ExprToClose) := exprsToClose.mapM fun ⟨e, isType⟩ => do {
  e ← Std.withShareCommon e;
  pure ⟨e, isType⟩
};
let exprsToClose := shareCommonExprs.run;
let mkExprs : ClosureM (Array Expr × MetavarContext) := do {
  exprs ← exprsToClose.mapM fun ⟨e, _⟩ => collectExpr e;
  mctx  ← getMCtx;
  pure (exprs, mctx)
};
match (mkExprs { lctxInput := lctx, zeta := zeta }).run { mctx := mctx } with
| EStateM.Result.ok (exprs, mctx) s =>
  let fvars := s.lctxOutput.getFVars;
  let exprs := exprs.mapIdx fun i e =>
    let isType := (exprsToClose.get! i).isType;
    if isType then
      s.lctxOutput.mkForall fvars e
    else
      s.lctxOutput.mkLambda fvars e;
  Except.ok {
    levelParams  := s.levelParams,
    exprs        := exprs,
    levelClosure := s.levelClosure,
    exprClosure  := s.exprClosure,
    mctx         := mctx
  }
| EStateM.Result.error ex s => Except.error ex

structure MkValueTypeClosureResult :=
(levelParams  : Array Name)
(type         : Expr)
(value        : Expr)
(levelClosure : Array Level)
(exprClosure  : Array Expr)
(mctx         : MetavarContext)

def mkValueTypeClosure (mctx : MetavarContext) (lctx : LocalContext) (type : Expr) (value : Expr) (zeta : Bool := false)
    : Except String MkValueTypeClosureResult := do
r ← mkClosure mctx lctx #[ { expr := type, isType := true }, { expr := value, isType := false } ] zeta;
pure {
  levelParams  := r.levelParams,
  type         := r.exprs.get! 0,
  value        := r.exprs.get! 1,
  levelClosure := r.levelClosure,
  exprClosure  := r.exprClosure,
  mctx         := r.mctx
}

end Closure
end Lean
