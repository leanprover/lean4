/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Meta.Check
import Lean.ReservedNameAction
import Lean.AddDecl
import Lean.Meta.Transform

/-!
# Transforming non-dependent `let`s into `have`s

A `let` expression `let x := v; b` is *dependent* if `fun x => b` is not type correct.
Non-dependent `let`s are those that can be transformed into `have x := v; b`.
This module has a procedure that detects which `let`s are non-dependent and does the transformation.

Dependence checking is approximated using the `withTrackingZetaDelta` trick:
we take `let x := v; b`, add a `x := v` declaration to the local context,
and then type check `b` with `withTrackingZetaDelta` enabled.
If `x` is not unfolded, then we know that `b` does not depend on `v`.
This is a conservative check, since `isDefEq` may unfold local definitions unnecessarily.

We do not use `Lean.Meta.check` directly. A naive algorithm would be to do `Meta.check (b.instantiate1 x)`
for each `let` body, which would involve rechecking subexpressions multiple times when there are nested `let`s.
Instead, we re-implement a type checking algorithm here to be able to interleave checking and transformation.

The trace class `trace.Meta.letToHave` reports statistics.

The transformation has very limited support for metavariables.
Any `let` that contains a metavariable remains a `let`.
-/

namespace Lean.Meta

namespace LetToHave

/-- Returns `true` if there are any subexpressions that this module can try to transform. -/
private def hasDepLet (e : Expr) : Bool :=
  Option.isSome <| e.find? (· matches .letE (nonDep := false) ..)

private structure Result where
  /-- The transformed expression. -/
  expr : Expr
  /-- The type of `expr`, if it has been computed. -/
  type? : Option Expr
  deriving Inhabited

private local instance : CoeHead Result Expr where coe := Result.expr

private structure Context where
  /-- The dependent lets we are currently under.
  If this list is nonempty, then full typechecking is necessary. -/
  letFVars : List FVarId := []

private structure State where
  count : Nat := 0
  /-- Cached results of `visit`. -/
  results : Std.HashMap ExprStructEq Result := {}

private abbrev M := ReaderT Context (StateRefT State MetaM)

private def Result.type (r : Result) : M Expr := do
  if let some type := r.type? then
    return type
  else
    let type ← inferType r.expr
    let r := { r with type? := type }
    modify fun s => { s with results := s.results.insert r.expr r }
    return type

/-- Returns `true` if we need to do full typechecking. -/
private def Context.check (ctx : Context) : Bool := !ctx.letFVars.isEmpty

/-- If we don't need full typechecking, returns `e`, otherwise evaluates `m`. -/
private def whenCheck (e : Expr) (m : M Result) : M Result := do
  if (← read).check then m else return { expr := e, type? := none }

/-- Executes `m` in a context where `letFVars := fvars`. -/
private def withLetFVars (fvars : List FVarId) (m : M α) : M α := do
  withReader (fun ctx => { ctx with letFVars := fvars }) m

/-- Increments the count of the number of `let`s transformed into `have`s. -/
private def incCount : M Unit :=
  modify fun s => { s with count := s.count + 1 }

/--
Finds a pre-existing result in the cache.
Note that the result might have no type, which is allowed if it was visited when `check` is false.
In that case, it is a term that does not need full typechecking, since it does not refer to
any dependent `let` fvars.
-/
private def findCache? (e : Expr) : M (Option Result) := do
  return (← get).results[(e : ExprStructEq)]?

/--
Finds `e` in the cache, or otherwise computes `m`.
-/
private def checkCache (e : Expr) (m : M Result) : M Result := do
  if let some r ← findCache? e then
    return r
  else
    if e.approxDepth ≤ 2 then
      -- Then up to 9 expression nodes.
      unless e.hasFVar || e.hasExprMVar || hasDepLet e do
        return { expr := e, type? := none }
    let r ← m
    modify fun st => { st with results := st.results.insert e r }
    return r

/-- Like `findMCache?` but checks that `e` doesn't have any loose bvars. -/
private def findCache?' (e : Expr) : M (Option Result) :=
  if e.hasLooseBVars then pure none else findCache? e

private def visitFVar (e : Expr) : MetaM Result := do
  let some decl ← e.fvarId!.findDecl? | e.fvarId!.throwUnknown
  return { expr := e, type? := decl.type }

private def checkMVar (_mvarId : MVarId) (_args : Array Expr) : M Unit := do
  -- TODO: implement precise check, then remove mvar check in isDepLet
  return

private def visitMVar (e : Expr) : M Result := do
  let some decl ← e.mvarId!.findDecl? | throwUnknownMVar e.mvarId!
  if (← read).check then checkMVar e.mvarId! #[]
  return { expr := e, type? := decl.type }

private def visitConst (e : Expr) : M Result := do
  whenCheck e do
    let .const constName us := e | unreachable!
    let cinfo ← getConstVal constName
    if cinfo.levelParams.length == us.length then
      let type ← instantiateTypeLevelParams cinfo us
      return { expr := e, type? := type }
    else
      throwIncorrectNumberOfLevels constName us

/--
When checking, makes sure that `r.type?` is of the form `Expr.sort _`.
-/
private def ensureType (r : Result) : M Result := do
  if (← read).check then
    let type ← r.type
    let r := { r with type? := type }
    if type.isSort then
      return r
    else
      let .sort u ← whnf type | throwTypeExpected r
      let r := { r with type? := Expr.sort u }
      modify fun s => { s with results := s.results.insert r.expr r }
      return r
  else
    return r

/--
A conservative check for whether to keep a dependent `let` dependent.
The `body` may have loose bvars.
-/
def isDepLet (fvarId : FVarId) (body : Expr) : M Bool := do
  if (← getZetaDeltaFVarIds).contains fvarId then
    /-
    If an fvar is not zeta delta reduced during typechecking, then it is safe
    to assume it is non-dependent. However, if it *is* zeta delta reduced,
    then we conservatively assume it is a dependent `let` binding.
    -/
    return true
  else if body.hasExprMVar then
    /-
    We do not try to analyze whether the metavariable depends on the local definition.
    This is rather subtle, and instead we conservatively assume that the
    metavariable *does* depend on it.
    (The type of a delayed assignment metavariables does not indicate whether it depends on the value of an fvar.)
    -/
    return true
  else
    return false

/--
Note: We want to cache all prefixes of each application, hence no `instantiateRevRange`-type logic here.
-/
private def visitApp (f a : Result) : M Result := do
  if (← read).check then
    let mut fType ← f.type
    unless fType.isForall do
      fType ← whnf fType
    match fType with
    | Expr.forallE _ d b _ =>
      unless (← isDefEq d (← a.type)) do
        throwAppTypeMismatch f a
      return { expr := .app f a, type? := b.instantiate1 a }
    | _ => throwFunctionExpected (mkApp f a)
  else
    return { expr := Expr.app f a, type? := none }

mutual

private partial def visitType (e : Expr) : M Result := do
  let r ← visit e
  ensureType r

private partial def visitAppArgs (e : Expr) : M Result := do
  if (← read).check then
    if let .mvar mvarId := e.getAppFn then
      checkMVar mvarId e.getAppArgs
    let rec go (e : Expr) : M Result := do
      let Expr.app f a := e | visit e
      visitApp (← checkCache f <| go f) (← visit a)
    go e
  else
    e.withApp fun f args => do
      return { expr := mkAppN (← visit f) (← args.mapM (fun arg => return (← visit arg).expr)), type? := none }

private partial def visitForall (e : Expr) : M Result := do
  if e.hasFVar || e.hasExprMVar || hasDepLet e then
    go (← getLCtx) #[] #[] e
  else
    return { expr := e, type? := none }
where
  go (lctx : LocalContext) (fvars : Array Expr) (doms : Array Result) (e : Expr) : M Result := do
    if let some e' ← findCache?' e then
      return ← withLCtx lctx {} do finalize fvars doms e'
    else
      match e with
      | .forallE n t b bi =>
        let t ← withLCtx lctx {} do visitType (t.instantiateRev fvars)
        let fvarId ← mkFreshFVarId
        let lctx  := lctx.mkLocalDecl fvarId n t.expr bi
        go lctx (fvars.push (.fvar fvarId)) (doms.push t) b
      | _ =>
        withLCtx lctx {} do
          let e' ← visit (e.instantiateRev fvars)
          finalize fvars doms e'
  finalize (fvars : Array Expr) (doms : Array Result) (body : Result) : M Result := do
    let body ← ensureType body
    let e' := (← getLCtx).mkForall fvars body
    if (← read).check then
      let u ← doms.foldrM (init := (← body.type).sortLevel!) fun dom u =>
        return mkLevelIMax' (← dom.type).sortLevel! u
      return { expr := e', type? := Expr.sort u }
    else
      return { expr := e', type? := none }

/--
Visits lambdas, lets, and haves.

Enters the entire telescope at once.
Checking the cache is more limited because there can be loose bvars.
The tradeoff is that we save time instantiating bvars by doing it all at once,
at the expense of possibly not sharing terms.
-/
private partial def visitLambdaLet (e : Expr) : M Result := do
  if e.hasFVar || e.hasExprMVar || hasDepLet e then
    go (← getLCtx) #[] e (← read).letFVars
  else
    return { expr := e, type? := none }
where
  /--
  Enters a forall/lambda/let/have telescope, checking that each domain type is a type.
  For let/have, checks that each value has a type defeq to the domain type.
  Calls `finalize` once the telescope is constructed.
  -/
  go (lctx : LocalContext) (fvars : Array Expr) (e : Expr) (letFVars : List FVarId) : M Result := do
    if let some e' ← findCache?' e then
      return ← withLCtx lctx {} do finalize fvars e'
    else
      let inCtx (v : Expr → M Result) (e : Expr) : M Result :=
        withLCtx lctx {} <| withLetFVars letFVars <| v (e.instantiateRev fvars)
      match e with
      | .lam n t b bi =>
        let t ← inCtx visitType t
        let fvarId ← mkFreshFVarId
        let lctx  := lctx.mkLocalDecl fvarId n t.expr bi
        go lctx (fvars.push (.fvar fvarId)) b letFVars
      | .letE n t v b nonDep =>
        let t ← inCtx visitType t
        let v ← inCtx visit v
        if (← read).check then withLCtx' lctx do
          let vType ← v.type
          unless (← isDefEq t vType) do
            throwError "invalid let declaration, term{indentExpr v}{← mkHasTypeButIsExpectedMsg vType t}"
        let fvarId ← mkFreshFVarId
        let lctx  := lctx.mkLetDecl fvarId n t v nonDep
        let letFVars := if nonDep then letFVars else fvarId :: letFVars
        go lctx (fvars.push (.fvar fvarId)) b letFVars
      | _ =>
        let body ← inCtx visit e
        withLCtx lctx {} <| withLetFVars letFVars <| finalize fvars body
  /--
  Assumption: the telescope domains and values are well-typed and the innermost body is well-typed.
  This function rebuilds the expression and converts `let`s to `have`s when possible.
  -/
  finalize (fvars : Array Expr) (body : Result) : M Result := do
    trace[Meta.letToHave.debug] "finalize {fvars},{indentD m!"{body.expr} : {body.type?}"}"
    let mut expr := body.expr
    let mut type? := body.type?
    expr := expr.abstract fvars
    type? := type?.map (·.abstract fvars)
    for j in [0:fvars.size] do
      let i := fvars.size - j - 1
      let .fvar fvarId := fvars[i]! | unreachable!
      let some decl ← fvarId.findDecl? | fvarId.throwUnknown
      match decl with
      | .cdecl _ _ n t bi _ => do
        let t := t.abstractRange i fvars
        expr := Expr.lam n t expr bi
        type? := type?.map fun type => Expr.forallE n t type bi
      | .ldecl _ _ n t v nonDep _ => do
        let nonDep ←
          if ← pure nonDep <||> isDepLet fvarId v then
            pure nonDep
          else
            incCount
            pure true
        let t := t.abstractRange i fvars
        let v := v.abstractRange i fvars
        expr := Expr.letE n t v expr nonDep
        type? := type?.map fun type =>
          if type.hasLooseBVar 0 then
            Expr.letE n t v type nonDep
          else
            type.lowerLooseBVars 1 1
    return { expr, type? }

private partial def visitProj (structName : Name) (idx : Nat) (struct : Result) : M Result := do
  unless (← read).check do
    return { expr := Expr.proj structName idx struct, type? := none }
  let structType ← whnf (← struct.type)
  let prop ← if (← read).check then isProp structType else pure false
  let failed {α} (_ : Unit) : M α := throwError "invalid projection{indentExpr (mkProj structName idx struct)}\nfrom type{indentExpr structType}"
  matchConstStructure structType.getAppFn failed fun structVal structLvls ctorVal => do
    unless structVal.name == structName do failed ()
    let structTypeArgs := structType.getAppArgs
    if structVal.numParams + structVal.numIndices != structTypeArgs.size then
      failed ()
    let mut ctorType ← inferType <| mkAppN (mkConst ctorVal.name structLvls) structTypeArgs[:structVal.numParams]
    let mut args := #[]
    let mut j := 0
    let mut lastFieldTy : Expr := default
    for i in [:idx+1] do
      unless ctorType.isForall do
        ctorType ← whnf <| ctorType.instantiateRevRange j i args
        j := i
      let .forallE _ dom body _ := ctorType | failed ()
      let dom := dom.instantiateRevRange j i args
      if prop then unless ← isProp dom do failed ()
      args := args.push <| Expr.proj structName i struct
      ctorType := body
      lastFieldTy := dom
    lastFieldTy := lastFieldTy.cleanupAnnotations
    return { expr := Expr.proj structName idx struct, type? := lastFieldTy }

private partial def visit (e : Expr) : M Result := do
  withTraceNode `Meta.letToHave.debug (fun res =>
      return m!"{if res.isOk then checkEmoji else crossEmoji} visit{indentExpr e}") do
    match e with
    | .bvar .. => throwError "unexpected bound variable {e}"
    | .fvar .. => visitFVar e
    | .mvar .. => visitMVar e
    | .sort u => return { expr := e, type? := Expr.sort u.succ }
    | .const .. => visitConst e
    | .app .. => checkCache e do visitAppArgs e
    | .forallE .. => checkCache e do visitForall e
    | .lam .. | .letE .. => checkCache e do visitLambdaLet e
    | .lit v => return { expr := e, type? := v.type }
    | .mdata _ e' => let e' ← visit e'; return { e' with expr := e.updateMData! e' }
    | .proj structName idx struct => checkCache e do visitProj structName idx (← visit struct)

end

private def main (e : Expr) : MetaM Expr := do
  Prod.fst <$> withTraceNode `Meta.letToHave (fun
      | .ok (_, msg) => pure m!"{checkEmoji} {msg}"
      | .error ex => pure m!"{crossEmoji} {ex.toMessageData}") do
    if hasDepLet e then
      withTrackingZetaDelta <|
      withTransparency TransparencyMode.all <|
      withInferTypeConfig do
        let (r, s) ← visit e |>.run {} |>.run {}
        if s.count == 0 then
          trace[Meta.letToHave] "result: (no change)"
        else
          trace[Meta.letToHave] "result:{indentExpr r.expr}"
        return (r.expr, m!"transformed {s.count} `let` expressions into `have` expressions")
    else
      return (e, "no `let` expressions")

end LetToHave

/--
Transforms non-dependent `let` expressions into `have` expressions.
If `e` is not type correct, returns `e`.
The `Meta.letToHave` trace class logs errors and messages.
-/
def letToHave (e : Expr) : MetaM Expr := do
  profileitM Exception "let-to-have transformation" (← getOptions) do
    let e ← instantiateMVars e
    LetToHave.main e

builtin_initialize
  registerTraceClass `Meta.letToHave
  registerTraceClass `Meta.letToHave.debug


/-!
Staging hack: we need some `have` versions of some Init theorems.
Using `name.let_to_have_thm` gives the theorem with the type transformed.
-/

def isLetToHaveName (env : Environment) (name : Name) : Bool := Id.run do
    let .str p "let_to_have_thm" := name | return false
    return env.findAsync? p |>.isSome

def deriveLetToHaveTheorem (letToHaveName : Name) (constName : Name) : MetaM Unit := do
  realizeConst constName letToHaveName do
    let ci ← getConstInfo constName
    let type ← letToHave ci.type
    -- Then transform `letFun`s to `have`s.
    let type ← Core.transform type
      (post := fun e =>
        if let some (args, n, t, v, b) := e.letFunAppArgs? then
          return .done <| mkAppN (.letE n t v b true) args
        else
          return .continue)
    let value := mkConst constName (ci.levelParams.map Level.param)
    addDecl <| Declaration.thmDecl {
      name := letToHaveName
      levelParams := ci.levelParams
      type
      value
    }

builtin_initialize
  registerReservedNamePredicate isLetToHaveName

builtin_initialize
  registerReservedNameAction fun name => do
    if isLetToHaveName (← getEnv) name then
      let .str p _ := name | return false
      MetaM.run' <| deriveLetToHaveTheorem name p
      return true
    return false

end Lean.Meta
