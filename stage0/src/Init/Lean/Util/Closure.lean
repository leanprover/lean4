/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Init.Lean.MetavarContext
import Init.Lean.Environment
import Init.Lean.Util.FoldConsts

namespace Lean
namespace Closure

structure Context :=
(mctx      : MetavarContext)
(lctxInput : LocalContext)

structure State :=
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
    modify $ fun s => { visitedLevel := s.visitedLevel.insert u v, .. s };
    pure v

def mkNewLevelParam (u : Level) : ClosureM Level := do
s ← get;
let p := (`u).appendIndexAfter s.nextLevelIdx;
modify $ fun s => { levelParams := s.levelParams.push p, nextLevelIdx := s.nextLevelIdx + 1, levelClosure := s.levelClosure.push u, .. s };
pure $ mkLevelParam p

partial def collectLevelAux : Level → ClosureM Level
| u@(Level.succ v _)   => do v ← visitLevel collectLevelAux v; pure $ u.updateSucc! v
| u@(Level.max v w _)  => do v ← visitLevel collectLevelAux v; w ← visitLevel collectLevelAux w; pure $ u.updateMax! v w
| u@(Level.imax v w _) => do v ← visitLevel collectLevelAux v; w ← visitLevel collectLevelAux w; pure $ u.updateIMax! v w
| u@(Level.mvar _ _)   => mkNewLevelParam u
| u@(Level.param _ _)  => mkNewLevelParam u
| u@(Level.zero _)     => pure u

def collectLevel (u : Level) : ClosureM Level :=
visitLevel collectLevelAux u

def mkFreshFVarId : ClosureM FVarId := do
s ← get;
let id := s.ngen.curr;
modify $ fun s => { ngen := s.ngen.next, .. s };
pure id

/--
  Remark: This method does not guarantee unique user names.
  The correctness of the procedure does not rely on unique user names.
  Recall that the pretty printer takes care of unintended collisions. -/
def mkNextUserName : ClosureM Name := do
s ← get;
let n := (`_x).appendIndexAfter s.nextExprIdx;
modify $ fun s => { nextExprIdx := s.nextExprIdx + 1, .. s };
pure n

def getUserName (userName? : Option Name) : ClosureM Name :=
match userName? with
| some userName => pure userName
| none          => mkNextUserName

def mkLocalDecl (userName? : Option Name) (type : Expr) : ClosureM Expr := do
userName ← getUserName userName?;
fvarId   ← mkFreshFVarId;
modify $ fun s => { lctxOutput := s.lctxOutput.mkLocalDecl fvarId userName type, .. s };
pure $ mkFVar fvarId

def mkLetDecl (userName : Name) (type : Expr) (value : Expr) : ClosureM Expr := do
fvarId   ← mkFreshFVarId;
modify $ fun s => { lctxOutput := s.lctxOutput.mkLetDecl fvarId userName type value, .. s };
pure $ mkFVar fvarId

@[inline] def visitExpr (f : Expr → ClosureM Expr) (e : Expr) : ClosureM Expr :=
if !e.hasLevelParam && !e.hasFVar && !e.hasMVar then pure e
else do
  s ← get;
  match s.visitedExpr.find? e with
  | some r => pure r
  | none   => do
    r ← f e;
    modify $ fun s => { visitedExpr := s.visitedExpr.insert e r, .. s };
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
    ctx ← read;
    match ctx.mctx.findDecl? mvarId with
    | none          => throw "unknown metavariable"
    | some mvarDecl => do
      type ← collect mvarDecl.type;
      x    ← mkLocalDecl none type;
      modify $ fun s => { exprClosure := s.exprClosure.push e, .. s };
      pure x
  | Expr.fvar fvarId _ => do
    ctx ← read;
    match ctx.lctxInput.find? fvarId with
    | none => throw "unknown free variable"
    | some (LocalDecl.cdecl _ _ userName type _) => do
      type ← collect type;
      x    ← mkLocalDecl userName type;
      modify $ fun s => { exprClosure := s.exprClosure.push e, .. s };
      pure x
    | some (LocalDecl.ldecl _ _ userName type value) => do
      type  ← collect type;
      value ← collect value;
      -- Note that let-declarations do not need to be provided to the closure being constructed.
      mkLetDecl userName type value
  | e => pure e

def collectExpr (e : Expr) : ClosureM Expr :=
visitExpr collectExprAux e

structure MkClosureResult :=
(levelParams  : Array Name)
(type         : Expr)
(value        : Expr)
(levelClosure : Array Level)
(exprClosure  : Array Expr)

def mkClosure (mctx : MetavarContext) (lctx : LocalContext) (type : Expr) (value : Expr) : Except String MkClosureResult :=
let shareCommonTypeValue : ShareCommonM (Expr × Expr) := do {
  type  ← withShareCommon type;
  value ← withShareCommon value;
  pure (type, value)
};
let (type, value) := shareCommonTypeValue.run;
let mkTypeValue : ClosureM (Expr × Expr) := do {
  type  ← collectExpr type;
  value ← collectExpr value;
  pure (type, value)
};
match (mkTypeValue { mctx := mctx, lctxInput := lctx }).run {} with
| EStateM.Result.ok (type, value) s =>
  let fvars := s.lctxOutput.getFVars;
  let type  := s.lctxOutput.mkForall fvars type;
  let value := s.lctxOutput.mkLambda fvars value;
  Except.ok {
    levelParams  := s.levelParams,
    type         := type,
    value        := value,
    levelClosure := s.levelClosure,
    exprClosure  := s.exprClosure }
| EStateM.Result.error ex s => Except.error ex

end Closure

def mkAuxDefinition (env : Environment) (opts : Options) (mctx : MetavarContext) (lctx : LocalContext) (name : Name) (type : Expr) (value : Expr)
    : Except KernelException (Expr × Environment) :=
match Closure.mkClosure mctx lctx type value with
| Except.error ex  => throw $ KernelException.other ex
| Except.ok result => do
  let decl := Declaration.defnDecl {
    name     := name,
    lparams  := result.levelParams.toList,
    type     := result.type,
    value    := result.value,
    hints    := ReducibilityHints.regular (getMaxHeight env result.value + 1),
    isUnsafe := env.hasUnsafe result.type || env.hasUnsafe result.value
  };
  env ← env.addAndCompile opts decl;
  let c := mkAppN (mkConst name result.levelClosure.toList) result.exprClosure;
  pure (c, env)

end Lean
