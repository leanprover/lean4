/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.ShareCommon
import Lean.MetavarContext
import Lean.Environment
import Lean.Util.FoldConsts
import Lean.Meta.Basic
import Lean.Meta.Check

namespace Lean
namespace Meta
namespace Closure

structure ToProcessElement :=
(fvarId : FVarId) (newFVarId : FVarId)

instance ToProcessElement.inhabited : Inhabited ToProcessElement :=
⟨⟨arbitrary _, arbitrary _⟩⟩

structure Context :=
(zeta : Bool)

structure State :=
(visitedLevel          : LevelMap Level := {})
(visitedExpr           : ExprStructMap Expr := {})
(levelParams           : Array Name := #[])
(nextLevelIdx          : Nat := 1)
(levelArgs             : Array Level := #[])
(newLocalDecls         : Array LocalDecl := #[])
(newLocalDeclsForMVars : Array LocalDecl := #[])
(newLetDecls           : Array LocalDecl := #[])
(nextExprIdx           : Nat := 1)
(exprMVarArgs          : Array Expr := #[])
(exprFVarArgs          : Array Expr := #[])
(toProcess             : Array ToProcessElement := #[])

abbrev ClosureM := ReaderT Context $ StateRefT State MetaM

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

def mkNewLevelParam (u : Level) : ClosureM Level := do
s ← get;
let p := (`u).appendIndexAfter s.nextLevelIdx;
modify $ fun s => { s with levelParams := s.levelParams.push p, nextLevelIdx := s.nextLevelIdx + 1, levelArgs := s.levelArgs.push u };
pure $ mkLevelParam p

partial def collectLevelAux : Level → ClosureM Level
| u@(Level.succ v _)      => do v ← visitLevel collectLevelAux v; pure $ u.updateSucc! v
| u@(Level.max v w _)     => do v ← visitLevel collectLevelAux v; w ← visitLevel collectLevelAux w; pure $ u.updateMax! v w
| u@(Level.imax v w _)    => do v ← visitLevel collectLevelAux v; w ← visitLevel collectLevelAux w; pure $ u.updateIMax! v w
| u@(Level.mvar mvarId _) => mkNewLevelParam u
| u@(Level.param _ _)     => mkNewLevelParam u
| u@(Level.zero _)        => pure u

def collectLevel (u : Level) : ClosureM Level := do
-- u ← instantiateLevelMVars u;
visitLevel collectLevelAux u

def preprocess (e : Expr) : ClosureM Expr := do
e ← instantiateMVars e;
ctx ← read;
-- If we are not zeta-expanding let-decls, then we use `check` to find
-- which let-decls are dependent. We say a let-decl is dependent if its lambda abstraction is type incorrect.
when (!ctx.zeta) $ liftM $ check e;
pure e

/--
  Remark: This method does not guarantee unique user names.
  The correctness of the procedure does not rely on unique user names.
  Recall that the pretty printer takes care of unintended collisions. -/
def mkNextUserName : ClosureM Name := do
s ← get;
let n := (`_x).appendIndexAfter s.nextExprIdx;
modify $ fun s => { s with nextExprIdx := s.nextExprIdx + 1 };
pure n

def pushToProcess (elem : ToProcessElement) : ClosureM Unit :=
modify fun s => { s with toProcess := s.toProcess.push elem }

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
    mvarDecl ← getMVarDecl mvarId;
    type ← preprocess mvarDecl.type;
    type ← collect type;
    newFVarId ← mkFreshFVarId;
    userName ← mkNextUserName;
    modify fun s => { s with
      newLocalDeclsForMVars := s.newLocalDeclsForMVars.push $ LocalDecl.cdecl (arbitrary _) newFVarId userName type BinderInfo.default,
      exprMVarArgs          := s.exprMVarArgs.push e
    };
    pure $ mkFVar newFVarId
  | Expr.fvar fvarId _ => do
    ctx ← read;
    decl ← getLocalDecl fvarId;
    match ctx.zeta, decl.value? with
    | true, some value => do value ← preprocess value; collect value
    | _,    _          => do
      newFVarId ← mkFreshFVarId;
      pushToProcess ⟨fvarId, newFVarId⟩;
      pure $ mkFVar newFVarId
  | e => pure e

def collectExpr (e : Expr) : ClosureM Expr := do
e ← preprocess e;
visitExpr collectExprAux e

partial def pickNextToProcessAux (lctx : LocalContext)
    : Nat → Array ToProcessElement → ToProcessElement → ToProcessElement × Array ToProcessElement
| i, toProcess, elem =>
  if h : i < toProcess.size then
    let elem' := toProcess.get ⟨i, h⟩;
    if (lctx.get! elem.fvarId).index < (lctx.get! elem'.fvarId).index then
      pickNextToProcessAux (i+1) (toProcess.set ⟨i, h⟩ elem) elem'
    else
      pickNextToProcessAux (i+1) toProcess elem
  else
    (elem, toProcess)

def pickNextToProcess? : ClosureM (Option ToProcessElement) := do
lctx ← getLCtx;
s ← get;
if s.toProcess.isEmpty then pure none
else
  modifyGet fun s =>
    let elem      := s.toProcess.back;
    let toProcess := s.toProcess.pop;
    let (elem, toProcess) := pickNextToProcessAux lctx 0 toProcess elem;
    (some elem, { s with toProcess := toProcess })

def pushFVarArg (e : Expr) : ClosureM Unit :=
modify fun s => { s with exprFVarArgs := s.exprFVarArgs.push e }

def pushLocalDecl (newFVarId : FVarId) (userName : Name) (type : Expr) (bi := BinderInfo.default) : ClosureM Unit := do
type ← collectExpr type;
modify fun s => { s with newLocalDecls := s.newLocalDecls.push $ LocalDecl.cdecl (arbitrary _) newFVarId userName type bi }

partial def process : Unit → ClosureM Unit
| _ => do
  elem? ← pickNextToProcess?;
  match elem? with
  | none => pure ()
  | some ⟨fvarId, newFVarId⟩ => do
    localDecl ← getLocalDecl fvarId;
    match localDecl with
    | LocalDecl.cdecl _ _ userName type bi => do
      pushLocalDecl newFVarId userName type bi;
      pushFVarArg (mkFVar fvarId);
      process ()
    | LocalDecl.ldecl _ _ userName type val _ => do
      zetaFVarIds ← getZetaFVarIds;
      if !zetaFVarIds.contains fvarId then do
        /- Non-dependent let-decl

           Recall that if `fvarId` is in `zetaFVarIds`, then we zeta-expanded it
           during type checking (see `check` at `collectExpr`).

           Our type checker may zeta-expand declarations that are not needed, but this
           check is conservative, and seems to work well in practice. -/
        pushLocalDecl newFVarId userName type;
        pushFVarArg (mkFVar fvarId);
        process ()
      else do
        /- Dependent let-decl -/
        type ← collectExpr type;
        val  ← collectExpr val;
        modify fun s => { s with newLetDecls := s.newLetDecls.push $ LocalDecl.ldecl (arbitrary _) newFVarId userName type val false };
        /- We don't want to interleave let and lambda declarations in our closure. So, we expand any occurrences of newFVarId
           at `newLocalDecls` -/
        modify fun s => { s with newLocalDecls := s.newLocalDecls.map (replaceFVarIdAtLocalDecl newFVarId val) };
        process ()

@[inline] def mkBinding (isLambda : Bool) (decls : Array LocalDecl) (b : Expr) : Expr :=
let xs := decls.map LocalDecl.toExpr;
let b  := b.abstract xs;
decls.size.foldRev
  (fun i b =>
    let decl := decls.get! i;
    match decl with
    | LocalDecl.cdecl _ _ n ty bi  =>
      let ty := ty.abstractRange i xs;
      if isLambda then
        Lean.mkLambda n bi ty b
      else
        Lean.mkForall n bi ty b
    | LocalDecl.ldecl _ _ n ty val nonDep =>
      if b.hasLooseBVar 0 then
        let ty  := ty.abstractRange i xs;
        let val := val.abstractRange i xs;
        mkLet n ty val b nonDep
      else
        b.lowerLooseBVars 1 1)
  b

def mkLambda (decls : Array LocalDecl) (b : Expr) : Expr :=
mkBinding true decls b

def mkForall (decls : Array LocalDecl) (b : Expr) : Expr :=
mkBinding false decls b

structure MkValueTypeClosureResult :=
(levelParams : Array Name)
(type        : Expr)
(value       : Expr)
(levelArgs   : Array Level)
(exprArgs    : Array Expr)

def mkValueTypeClosureAux (type : Expr) (value : Expr) : ClosureM (Expr × Expr) := do
resetZetaFVarIds;
withTrackingZeta do
  type  ← collectExpr type;
  value ← collectExpr value;
  process ();
  pure (type, value)

def mkValueTypeClosure (type : Expr) (value : Expr) (zeta : Bool) : MetaM MkValueTypeClosureResult := do
((type, value), s) ← ((mkValueTypeClosureAux type value).run { zeta := zeta }).run {};
let newLocalDecls := s.newLocalDecls.reverse ++ s.newLocalDeclsForMVars;
let newLetDecls   := s.newLetDecls.reverse;
let type  := mkForall newLocalDecls (mkForall newLetDecls type);
let value := mkLambda newLocalDecls (mkLambda newLetDecls value);
pure {
  type        := type,
  value       := value,
  levelParams := s.levelParams,
  levelArgs   := s.levelArgs,
  exprArgs    := s.exprFVarArgs.reverse ++ s.exprMVarArgs
}

end Closure

variables {m : Type → Type} [MonadLiftT MetaM m]

private def mkAuxDefinitionImp (name : Name) (type : Expr) (value : Expr) (zeta : Bool) : MetaM Expr := do
result ← Closure.mkValueTypeClosure type value zeta;
env ← getEnv;
let decl := Declaration.defnDecl {
  name     := name,
  lparams  := result.levelParams.toList,
  type     := result.type,
  value    := result.value,
  hints    := ReducibilityHints.regular (getMaxHeight env result.value + 1),
  isUnsafe := env.hasUnsafe result.type || env.hasUnsafe result.value
};
trace! `Meta.debug (name ++ " : " ++ result.type ++ " := " ++ result.value);
addAndCompile decl;
pure $ mkAppN (mkConst name result.levelArgs.toList) result.exprArgs

/--
  Create an auxiliary definition with the given name, type and value.
  The parameters `type` and `value` may contain free and meta variables.
  A "closure" is computed, and a term of the form `name.{u_1 ... u_n} t_1 ... t_m` is
  returned where `u_i`s are universe parameters and metavariables `type` and `value` depend on,
  and `t_j`s are free and meta variables `type` and `value` depend on. -/
def mkAuxDefinition (name : Name) (type : Expr) (value : Expr) (zeta := false) : m Expr := liftMetaM do
trace! `Meta.debug (name ++ " : " ++ type ++ " := " ++ value);
mkAuxDefinitionImp name type value zeta

/-- Similar to `mkAuxDefinition`, but infers the type of `value`. -/
def mkAuxDefinitionFor (name : Name) (value : Expr) : m Expr := liftMetaM do
type ← inferType value;
let type := type.headBeta;
mkAuxDefinition name type value

end Meta
end Lean
