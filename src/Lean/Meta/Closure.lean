/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.MetavarContext
import Lean.Environment
import Lean.AddDecl
import Lean.Util.FoldConsts
import Lean.Meta.Basic
import Lean.Meta.Check

/-!

This module provides functions for "closing" open terms and
creating auxiliary definitions. Here, we say a term is "open" if
it contains free/meta-variables.

The "closure" is performed by lambda abstracting the
free/meta-variables. Recall that in dependent type theory
lambda abstracting a let-variable may produce type incorrect terms.
For example, given the context
```lean
(n : Nat := 20)
(x : Vector α n)
(y : Vector α 20)
```
the term `x = y` is correct. However, its closure using lambda abstractions
is not.
```lean
fun (n : Nat) (x : Vector α n) (y : Vector α 20) => x = y
```
A previous version of this module would address this issue by
always use let-expressions to abstract let-vars. In the example above,
it would produce
```lean
let n : Nat := 20; fun (x : Vector α n) (y : Vector α 20) => x = y
```
This approach produces correct result, but produces unsatisfactory
results when we want to create auxiliary definitions.
For example, consider the context
```lean
(x : Nat)
(y : Nat := fact x)
```
and the term `h (g y)`, now suppose we want to create an auxiliary definition for `y`.
 The previous version of this module would compute the auxiliary definition
```lean
def aux := fun (x : Nat) => let y : Nat := fact x; h (g y)
```
and would return the term `aux x` as a substitute for `h (g y)`.
This is correct, but we will re-evaluate `fact x` whenever we use `aux`.
In this module, we produce
```lean
def aux := fun (y : Nat) => h (g y)
```
Note that in this particular case, it is safe to lambda abstract the let-varible `y`.
This module uses the following approach to decide whether it is safe or not to lambda
abstract a let-variable.
1) We enable zetaDelta-expansion tracking in `MetaM`. That is, whenever we perform type checking
   if a let-variable needs to zetaDelta expanded, we store it in the set `zetaDeltaFVarIds`.
   We say a let-variable is zetaDelta expanded when we replace it with its value.
2) We use the `MetaM` type checker `check` to type check the expression we want to close,
   and the type of the binders.
3) If a let-variable is not in `zetaDeltaFVarIds`, we lambda abstract it.

Remark: We still use let-expressions for let-variables in `zetaDeltaFVarIds`, but we move the
`let` inside the lambdas. The idea is to make sure the auxiliary definition does not have
an interleaving of `lambda` and `let` expressions. Thus, if the let-variable occurs in
the type of one of the lambdas, we simply zeta-expand it there.
As a final example consider the context
```lean
(x_1 : Nat)
(x_2 : Nat)
(x_3 : Nat)
(x   : Nat := fact (10 + x_1 + x_2 + x_3))
(ty  : Type := Nat → Nat)
(f   : ty := fun x => x)
(n   : Nat := 20)
(z   : f 10)
```
and we use this module to compute an auxiliary definition for the term
```lean
(let y  : { v : Nat // v = n } := ⟨20, rfl⟩; y.1 + n + f x, z + 10)
```
we obtain
```lean
def aux (x : Nat) (f : Nat → Nat) (z : Nat) : Nat×Nat :=
let n : Nat := 20;
(let y : {v // v=n} := {val := 20, property := ex._proof_1}; y.val+n+f x, z+10)
```

BTW, this module also provides the `zetaDelta : Bool` flag. When set to true, it
expands all let-variables occurring in the target expression.
-/

namespace Lean.Meta
namespace Closure

structure ToProcessElement where
  fvarId : FVarId
  newFVarId : FVarId
  deriving Inhabited

structure Context where
  zetaDelta : Bool

structure State where
  visitedLevel          : LevelMap Level := {}
  visitedExpr           : ExprStructMap Expr := {}
  levelParams           : Array Name := #[]
  nextLevelIdx          : Nat := 1
  levelArgs             : Array Level := #[]
  newLocalDecls         : Array LocalDecl := #[]
  newLocalDeclsForMVars : Array LocalDecl := #[]
  newLetDecls           : Array LocalDecl := #[]
  nextExprIdx           : Nat := 1
  exprMVarArgs          : Array Expr := #[]
  exprFVarArgs          : Array Expr := #[]
  toProcess             : Array ToProcessElement := #[]

abbrev ClosureM := ReaderT Context $ StateRefT State MetaM

@[inline] def visitLevel (f : Level → ClosureM Level) (u : Level) : ClosureM Level := do
  if !u.hasMVar && !u.hasParam then
    pure u
  else
    let s ← get
    match s.visitedLevel[u]? with
    | some v => pure v
    | none   => do
      let v ← f u
      modify fun s => { s with visitedLevel := s.visitedLevel.insert u v }
      pure v

@[inline] def visitExpr (f : Expr → ClosureM Expr) (e : Expr) : ClosureM Expr := do
  if !e.hasLevelParam && !e.hasFVar && !e.hasMVar then
    pure e
  else
    let s ← get
    match s.visitedExpr.get? e with
    | some r => pure r
    | none   =>
      let r ← f e
      modify fun s => { s with visitedExpr := s.visitedExpr.insert e r }
      pure r

def mkNewLevelParam (u : Level) : ClosureM Level := do
  let s ← get
  let p := (`u).appendIndexAfter s.nextLevelIdx
  modify fun s => { s with levelParams := s.levelParams.push p, nextLevelIdx := s.nextLevelIdx + 1, levelArgs := s.levelArgs.push u }
  pure $ mkLevelParam p

partial def collectLevelAux : Level → ClosureM Level
  | u@(Level.succ v)   => return u.updateSucc! (← visitLevel collectLevelAux v)
  | u@(Level.max v w)  => return u.updateMax! (← visitLevel collectLevelAux v) (← visitLevel collectLevelAux w)
  | u@(Level.imax v w) => return u.updateIMax! (← visitLevel collectLevelAux v) (← visitLevel collectLevelAux w)
  | u@(Level.mvar ..)    => mkNewLevelParam u
  | u@(Level.param ..)   => mkNewLevelParam u
  | u@(Level.zero)     => pure u

def collectLevel (u : Level) : ClosureM Level := do
  -- u ← instantiateLevelMVars u
  visitLevel collectLevelAux u

def preprocess (e : Expr) : ClosureM Expr := do
  let e ← instantiateMVars e
  let ctx ← read
  -- If we are not zetaDelta-expanding let-decls, then we use `check` to find
  -- which let-decls are dependent. We say a let-decl is dependent if its lambda abstraction is type incorrect.
  if !ctx.zetaDelta then
    check e
  pure e

/--
  Remark: This method does not guarantee unique user names.
  The correctness of the procedure does not rely on unique user names.
  Recall that the pretty printer takes care of unintended collisions. -/
def mkNextUserName : ClosureM Name := do
  let s ← get
  let n := (`_x).appendIndexAfter s.nextExprIdx
  modify fun s => { s with nextExprIdx := s.nextExprIdx + 1 }
  pure n

def pushToProcess (elem : ToProcessElement) : ClosureM Unit :=
  modify fun s => { s with toProcess := s.toProcess.push elem }

partial def collectExprAux (e : Expr) : ClosureM Expr := do
  let collect (e : Expr) := visitExpr collectExprAux e
  match e with
  | Expr.proj _ _ s      => return e.updateProj! (← collect s)
  | Expr.forallE _ d b _ => return e.updateForallE! (← collect d) (← collect b)
  | Expr.lam _ d b _     => return e.updateLambdaE! (← collect d) (← collect b)
  | Expr.letE _ t v b _  => return e.updateLet! (← collect t) (← collect v) (← collect b)
  | Expr.app f a         => return e.updateApp! (← collect f) (← collect a)
  | Expr.mdata _ b       => return e.updateMData! (← collect b)
  | Expr.sort u          => return e.updateSort! (← collectLevel u)
  | Expr.const _ us      => return e.updateConst! (← us.mapM collectLevel)
  | Expr.mvar mvarId     =>
    let mvarDecl ← mvarId.getDecl
    let type ← preprocess mvarDecl.type
    let type ← collect type
    let newFVarId ← mkFreshFVarId
    let userName ← mkNextUserName
    modify fun s => { s with
      newLocalDeclsForMVars := s.newLocalDeclsForMVars.push $ .cdecl default newFVarId userName type .default .default,
      exprMVarArgs          := s.exprMVarArgs.push e
    }
    return mkFVar newFVarId
  | Expr.fvar fvarId =>
    match (← read).zetaDelta, (← fvarId.getValue?) with
    | true, some value => collect (← preprocess value)
    | _,    _          =>
      let newFVarId ← mkFreshFVarId
      pushToProcess ⟨fvarId, newFVarId⟩
      return mkFVar newFVarId
  | e => pure e

def collectExpr (e : Expr) : ClosureM Expr := do
  let e ← preprocess e
  visitExpr collectExprAux e

partial def pickNextToProcessAux (lctx : LocalContext) (i : Nat) (toProcess : Array ToProcessElement) (elem : ToProcessElement)
    : ToProcessElement × Array ToProcessElement :=
  if h : i < toProcess.size then
    let elem' := toProcess[i]
    if (lctx.get! elem.fvarId).index < (lctx.get! elem'.fvarId).index then
      pickNextToProcessAux lctx (i+1) (toProcess.set i elem) elem'
    else
      pickNextToProcessAux lctx (i+1) toProcess elem
  else
    (elem, toProcess)

def pickNextToProcess? : ClosureM (Option ToProcessElement) := do
  let lctx ← getLCtx
  let s ← get
  if s.toProcess.isEmpty then
    pure none
  else
    modifyGet fun s =>
      let elem      := s.toProcess.back!
      let toProcess := s.toProcess.pop
      let (elem, toProcess) := pickNextToProcessAux lctx 0 toProcess elem
      (some elem, { s with toProcess := toProcess })

def pushFVarArg (e : Expr) : ClosureM Unit :=
  modify fun s => { s with exprFVarArgs := s.exprFVarArgs.push e }

def pushLocalDecl (newFVarId : FVarId) (userName : Name) (type : Expr) (bi := BinderInfo.default) : ClosureM Unit := do
  let type ← collectExpr type
  modify fun s => { s with newLocalDecls := s.newLocalDecls.push <| .cdecl default newFVarId userName type bi .default }

partial def process : ClosureM Unit := do
  match (← pickNextToProcess?) with
  | none => pure ()
  | some ⟨fvarId, newFVarId⟩ =>
    match (← fvarId.getDecl) with
    | .cdecl _ _ userName type bi _ =>
      pushLocalDecl newFVarId userName type bi
      pushFVarArg (mkFVar fvarId)
      process
    | .ldecl _ _ userName type val _ _ =>
      let zetaDeltaFVarIds ← getZetaDeltaFVarIds
      if !zetaDeltaFVarIds.contains fvarId then
        /- Non-dependent let-decl

            Recall that if `fvarId` is in `zetaDeltaFVarIds`, then we zetaDelta-expanded it
            during type checking (see `check` at `collectExpr`).

            Our type checker may zetaDelta-expand declarations that are not needed, but this
            check is conservative, and seems to work well in practice. -/
        pushLocalDecl newFVarId userName type
        pushFVarArg (mkFVar fvarId)
        process
      else
        /- Dependent let-decl -/
        let type ← collectExpr type
        let val  ← collectExpr val
        modify fun s => { s with newLetDecls := s.newLetDecls.push <| .ldecl default newFVarId userName type val false .default }
        /- We don't want to interleave let and lambda declarations in our closure. So, we expand any occurrences of newFVarId
           at `newLocalDecls` -/
        modify fun s => { s with newLocalDecls := s.newLocalDecls.map (·.replaceFVarId newFVarId val) }
        process

@[inline] def mkBinding (isLambda : Bool) (decls : Array LocalDecl) (b : Expr) : Expr :=
  let xs := decls.map LocalDecl.toExpr
  let b  := b.abstract xs
  decls.size.foldRev (init := b) fun i b =>
    let decl := decls[i]!
    match decl with
    | .cdecl _ _ n ty bi _ =>
      let ty := ty.abstractRange i xs
      if isLambda then
        Lean.mkLambda n bi ty b
      else
        Lean.mkForall n bi ty b
    | .ldecl _ _ n ty val nonDep _ =>
      if b.hasLooseBVar 0 then
        let ty  := ty.abstractRange i xs
        let val := val.abstractRange i xs
        mkLet n ty val b nonDep
      else
        b.lowerLooseBVars 1 1

def mkLambda (decls : Array LocalDecl) (b : Expr) : Expr :=
  mkBinding true decls b

def mkForall (decls : Array LocalDecl) (b : Expr) : Expr :=
  mkBinding false decls b

structure MkValueTypeClosureResult where
  levelParams : Array Name
  type        : Expr
  value       : Expr
  levelArgs   : Array Level
  exprArgs    : Array Expr

def mkValueTypeClosureAux (type : Expr) (value : Expr) : ClosureM (Expr × Expr) := do
  resetZetaDeltaFVarIds
  withTrackingZetaDelta do
    let type  ← collectExpr type
    let value ← collectExpr value
    process
    pure (type, value)

def mkValueTypeClosure (type : Expr) (value : Expr) (zetaDelta : Bool) : MetaM MkValueTypeClosureResult := do
  let ((type, value), s) ← ((mkValueTypeClosureAux type value).run { zetaDelta }).run {}
  let newLocalDecls := s.newLocalDecls.reverse ++ s.newLocalDeclsForMVars
  let newLetDecls   := s.newLetDecls.reverse
  let type  := mkForall newLocalDecls (mkForall newLetDecls type)
  let value := mkLambda newLocalDecls (mkLambda newLetDecls value)
  pure {
    type        := type,
    value       := value,
    levelParams := s.levelParams,
    levelArgs   := s.levelArgs,
    exprArgs    := s.exprFVarArgs.reverse ++ s.exprMVarArgs
  }

end Closure

/--
  Create an auxiliary definition with the given name, type and value.
  The parameters `type` and `value` may contain free and meta variables.
  A "closure" is computed, and a term of the form `name.{u_1 ... u_n} t_1 ... t_m` is
  returned where `u_i`s are universe parameters and metavariables `type` and `value` depend on,
  and `t_j`s are free and meta variables `type` and `value` depend on. -/
def mkAuxDefinition (name : Name) (type : Expr) (value : Expr) (zetaDelta : Bool := false) (compile : Bool := true) : MetaM Expr := do
  let result ← Closure.mkValueTypeClosure type value zetaDelta
  let env ← getEnv
  let hints := ReducibilityHints.regular (getMaxHeight env result.value + 1)
  let decl := Declaration.defnDecl (← mkDefinitionValInferrringUnsafe name result.levelParams.toList
    result.type result.value  hints)
  addDecl decl
  if compile then
    compileDecl decl
  return mkAppN (mkConst name result.levelArgs.toList) result.exprArgs

/-- Similar to `mkAuxDefinition`, but infers the type of `value`. -/
def mkAuxDefinitionFor (name : Name) (value : Expr) (zetaDelta : Bool := false) : MetaM Expr := do
  let type ← inferType value
  let type := type.headBeta
  mkAuxDefinition name type value (zetaDelta := zetaDelta)

/--
  Create an auxiliary theorem with the given name, type and value. It is similar to `mkAuxDefinition`.
-/
def mkAuxTheorem (name : Name) (type : Expr) (value : Expr) (zetaDelta : Bool := false) : MetaM Expr := do
  let result ← Closure.mkValueTypeClosure type value zetaDelta
  let env ← getEnv
  let decl :=
    if env.hasUnsafe result.type || env.hasUnsafe result.value then
      -- `result` contains unsafe code, thus we cannot use a theorem.
      Declaration.defnDecl {
        name
        levelParams := result.levelParams.toList
        type        := result.type
        value       := result.value
        hints       := ReducibilityHints.opaque
        safety      := DefinitionSafety.unsafe
      }
    else
      Declaration.thmDecl {
        name
        levelParams := result.levelParams.toList
        type        := result.type
        value       := result.value
      }
  addDecl decl
  return mkAppN (mkConst name result.levelArgs.toList) result.exprArgs

/--
  Similar to `mkAuxTheorem`, but infers the type of `value`.
-/
def mkAuxTheoremFor (name : Name) (value : Expr) (zetaDelta : Bool := false) : MetaM Expr := do
  let type ← inferType value
  let type := type.headBeta
  mkAuxTheorem name type value zetaDelta

end Lean.Meta
