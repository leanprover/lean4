/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Meta.InferType

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

/--
An expression along with its type.
-/
private structure Expr' where
  val : Expr
  /-- The type of `val`. -/
  type : Expr
  deriving Inhabited

@[inline] private def Expr'.abstract (e : Expr') (fvars : Array Expr) : Expr' where
  val := e.val.abstract fvars
  type := e.type.abstract fvars

@[inline] private def Expr'.instantiate1 (e : Expr') (subst : Expr) : Expr' where
  val := e.val.instantiate1 subst
  type := e.type.instantiate1 subst

/--
Creates a `have` expression.
- `u` is the universe level for the type of the value `val`
- `v` is the universe level for the type of the body `b`
- The `b` type and value may have loose bvars.
-/
private def Expr'.mkHave (u v : Level) (n : Name) (val : Expr') (b : Expr') : Expr' where
  val :=
    mkApp4 (mkConst ``letFun [u, v])
      val.type (Expr.lam n val.type b.type .default)
      val.val
      (Expr.lam n val.type b.val .default)
  type :=
    if b.type.hasLooseBVar 0 then
      mkApp4 (mkConst ``letFun [u, v.succ])
        val.type (Expr.lam n val.type (Expr.sort v) .default)
        val.val
        (Expr.lam n val.type b.type .default)
    else
      b.type.lowerLooseBVars 1 1

/--
Creates a `let` expression. The `b` type and value may have loose bvars.
-/
private def Expr'.mkLet (n : Name) (val : Expr') (b : Expr') (nonDep : Bool) : Expr' where
  val := Expr.letE n val.type val.val b.val nonDep
  type :=
    if b.type.hasLooseBVar 0 then
      Expr.letE n val.type val.val b.type nonDep
    else
      b.type.lowerLooseBVars 1 1

private local instance : CoeHead Expr' Expr where coe := Expr'.val

private structure Context where
  /-- Whether to do full typechecking or not.
  Full typechecking is necessary when under a `let`.
  When false, the transformation can reduce to computing `inferType`. -/
  fullCheck : Bool := false

private structure State where
  count : Nat := 0

private abbrev M := ReaderT Context <| MonadCacheT ExprStructEq Expr' (StateRefT State MetaM)

private def whenFullCheck (m : M Unit) (b : Bool := false) : M Unit := do
  if b || (← read).fullCheck then m

private def withFullCheck (b : Bool) (m : M α) : M α := do
  withReader (fun ctx => { ctx with fullCheck := ctx.fullCheck || b }) m

/-- Increments the count of the number of `let`s transformed into `have`s. -/
private def incCount : M Unit :=
  modify fun s => { s with count := s.count + 1 }

private def checkMCache (e : Expr) (m : M Expr') : M Expr' :=
  checkCache { val := e : ExprStructEq } fun _ => m

private def findMCache? (e : Expr) : M (Option Expr') :=
  MonadCache.findCached? { val := e : ExprStructEq }

private def visitFVar (e : Expr) : MetaM Expr' := do
  let some decl ← e.fvarId!.findDecl? | throwError "fvar: unknown"
  -- We did `instantiateLCtxMVars`, so no need to `instantiateMVars` the type.
  return { val := e, type := decl.type }

private def visitMVar (e : Expr) : MetaM Expr' := do
  let some decl ← e.mvarId!.findDecl? | throwError "mvar: unknown"
  return { val := e, type := (← instantiateMVars decl.type) }

private def visitConst (e : Expr) (constName : Name) (us : List Level) : M Expr' := do
  let cinfo ← getConstVal constName
  if cinfo.levelParams.length == us.length then
    if us.isEmpty then
      return { val := e, type := cinfo.type }
    else
      let type ← instantiateTypeLevelParams cinfo us
      return { val := e, type }
  else
    throwError "const: invalid"

private def visitApp (f : Expr') (args : Array Expr') : M Expr' := do
  let argVals := args.map Expr'.val
  let mut type := f.type
  let mut j := 0
  for i in [:args.size] do
    unless type.isForall do
      type ← whnf <| type.instantiateRevRange j i argVals
      j := i
    let .forallE _ dom b _ := type | throwError "app: function expected"
    type := b
    whenFullCheck do
      let dom := dom.instantiateRevRange j i argVals
      unless ← isDefEq dom args[i]!.type do throwError "app: dom not defeq"
  type := type.instantiateRevRange j argVals.size argVals
  return { val := mkAppN f argVals, type }

private def getSortLevel (e : Expr) : MetaM Level := do
  let .sort u ← whnf e | throwError "not Sort"
  return u

private inductive BoundKind
  /-- `t` is the visited binding domain *with* annotations. -/
  | forall (t : Expr)
  /-- `t` is the visited binding domain *with* annotations. -/
  | lambda (t : Expr)
  | let
  /-- `v` is the value of the `have`. This is stored here because the value
  is not put into the local context. -/
  | have (v : Expr)
  deriving Inhabited

/--
A conservative check for whether to keep a `let` dependent.
The `body` may have loose bvars.
-/
def isDepLet (fvarId : FVarId) (body : Expr) : M Bool := do
  let some decl ← fvarId.findDecl? | throwError "isDepLet: unknown"
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
    (Delayed assignment metavariables only show the dependence inside their local contexts.)
    -/
    return true
  else if decl.userName.eraseMacroScopes == `__do_jp then
    /-
    Join points for `do` notation are represented using `let`s,
    and we should leave them as `let`s for the compiler's sake.
    TODO(kmill) Remove this hack once the new compiler is ready to be told about `have`s.
    -/
    return true
  else
    return false

mutual

private partial def visitApp' (f : Expr) (args : Array Expr) : M Expr' := do
    visitApp (← visit f) (← args.mapM visit)

private partial def visitApp'' (e : Expr) : M Expr' := do
  let arity := e.getAppNumArgs
  if e.isAppOf ``letFun && arity ≥ 4 then
    if arity == 4 then
      visitBound e
    else
      visitApp' (e.getBoundedAppFn (arity - 4)) (e.getBoundedAppArgs (arity - 4))
  else
    visitApp' e.getAppFn e.getAppArgs

/--
Visits foralls, lambdas, lets, and haves.

Enters the entire telescope at once.
Checking the cache is more limited because there can be loose bvars.
The tradeoff is that we save time instantiating bvars by doing it all at once,
at the expense of possibly not sharing terms.
-/
private partial def visitBound (e : Expr) : M Expr' := do
  visitBody (← getLCtx) #[] #[] #[] false e
where
  /--
  Enters a forall/lambda/let/have telescope, checking that each domain type is a type.
  For let/have, checks that each value has a type defeq to the domain type.
  Calls `finalize` once the telescope is constructed.
  -/
  visitBody (lctx : LocalContext) (fvars : Array Expr) (kinds : Array BoundKind) (levels : Array Level) (seenLet : Bool) (e : Expr) : M Expr' := do
    if !e.hasLooseBVars then
      if let some e' ← findMCache? e then
        return ← withLCtx lctx {} do finalize fvars kinds levels e'
    let visitAndInstantiate (e : Expr) : M Expr' := withLCtx lctx {} do
      withFullCheck seenLet do visit (e.instantiateRev fvars)
    match e with
    | .forallE n t b bi =>
      let t     ← visitAndInstantiate t
      let fvarId ← mkFreshFVarId
      let lctx  := lctx.mkLocalDecl fvarId n t.val.cleanupAnnotations bi
      let fvars := fvars.push (mkFVar fvarId)
      let kinds := kinds.push (.forall t)
      let levels := levels.push (← withLCtx lctx {} <| getSortLevel t.type)
      visitBody lctx fvars kinds levels seenLet b
    | .lam n t b bi =>
      let t     ← visitAndInstantiate t
      let fvarId ← mkFreshFVarId
      let lctx  := lctx.mkLocalDecl fvarId n t.val.cleanupAnnotations bi
      let fvars := fvars.push (mkFVar fvarId)
      let kinds := kinds.push (.lambda t)
      let levels := levels.push (← withLCtx lctx {} <| getSortLevel t.type)
      visitBody lctx fvars kinds levels seenLet b
    | .letE n t v b _ =>
      let t     ← visitAndInstantiate t
      let v     ← visitAndInstantiate v
      whenFullCheck (b := seenLet) do
        unless ← withLCtx lctx {} (isDefEq t v.type) do throwError "let: value type not defeq to type"
      let fvarId ← mkFreshFVarId
      let lctx  := lctx.mkLetDecl fvarId n t v
      let fvars := fvars.push (mkFVar fvarId)
      let kinds := kinds.push .let
      let levels := levels.push (← withLCtx lctx {} <| getSortLevel t.type)
      visitBody lctx fvars kinds levels true b
    | _ =>
      if let some (n, t, v, b) := e.letFun? then
        let t     ← visitAndInstantiate t
        let v     ← visitAndInstantiate v
        whenFullCheck (b := seenLet) do
          unless ← withLCtx lctx {} (isDefEq t v.type) do throwError "have: value type not defeq to type"
        let fvarId ← mkFreshFVarId
        let lctx  := lctx.mkLocalDecl fvarId n t
        let fvars := fvars.push (mkFVar fvarId)
        let kinds := kinds.push (.have v)
        let levels := levels.push (← withLCtx lctx {} <| getSortLevel t.type)
        visitBody lctx fvars kinds levels seenLet b
      else
        withFullCheck seenLet do
          withLCtx lctx {} do
            let e' ← visit (e.instantiateRev fvars)
            finalize fvars kinds levels e'
  /--
  Assumption: the telescope domains and values are well-typed and the innermost body is well-typed.
  This function checks that the telescope is well-constructed (the bodies of foralls are types)
  and converts `let`s to `have`s when possible.
  -/
  finalize (fvars : Array Expr) (kinds : Array BoundKind) (levels : Array Level) (body : Expr') : M Expr' := do
    let mut body := body
    trace[Meta.letToHave.debug] "finalize {fvars},{indentD m!"{body.val} : {body.type}"}"
    -- When building `have`s, we need to know the type of `type`.
    -- We must compute this before we abstract the fvars.
    let mut typeLevel ← getSortLevel (← inferType body.type)
    -- If there is a forall, then there cannot be any lambdas after it, and `body` must be a type.
    -- This is necessary and sufficient for all the foralls to be well-constructed.
    if let some i := kinds.findIdx? (· matches .forall _) then
      let u ← getSortLevel body.type
      -- Invariant: the `type` will always be of the form `Sort _` when visiting forall.
      body := { body with type := mkSort u }
      if kinds.any (start := i + 1) (· matches .lambda _) then
        throwError "forall: body is lambda"
    -- Now reconstruct the binding expressions
    body := Expr'.abstract body fvars
    for j in [0:fvars.size] do
      let i := fvars.size - j - 1
      let fvar := fvars[i]!
      let some decl ← fvar.fvarId!.findDecl? | throwError "fvar: unknown in visitBound"
      let kind := kinds[i]!
      let level := levels[i]!
      match kind with
      | .forall t =>
        let t := t.abstractRange i fvars
        let Expr.sort u := body.type | throwError "forall: invariant failure"
        let u' := mkLevelIMax' level u
        body := { val := Expr.forallE decl.userName t body.val decl.binderInfo,
                  type := Expr.sort u' }
        typeLevel := u'.succ
      | .lambda t =>
        let t := t.abstractRange i fvars
        body := { val := Expr.lam decl.userName t body.val decl.binderInfo,
                  type := Expr.forallE decl.userName t body.type decl.binderInfo }
        typeLevel := mkLevelIMax' level typeLevel
      | .let =>
        -- typeLevel remains the same
        let t := decl.type.abstractRange i fvars
        let v := decl.value.abstractRange i fvars
        if ← isDepLet fvar.fvarId! body.val then
          body := Expr'.mkLet decl.userName { val := v, type := t } body false
        else
          incCount
          body := Expr'.mkHave level.normalize typeLevel.normalize decl.userName { val := v, type := t } body
      | .have v =>
        -- typeLevel remains the same
        let t := decl.type.abstractRange i fvars
        let v := v.abstractRange i fvars
        body := Expr'.mkHave level.normalize typeLevel.normalize decl.userName { val := v, type := t } body
    return body

private partial def visitProj (structName : Name) (idx : Nat) (struct : Expr') : M Expr' := do
  let structType ← whnf struct.type
  let prop ← isProp structType
  let failed {α} (_ : Unit) : M α := throwError "proj: invalid"
  matchConstStructure structType.getAppFn failed fun structVal structLvls ctorVal => do
    unless structVal.name == structName do failed ()
    let structTypeArgs := structType.getAppArgs
    if structVal.numParams + structVal.numIndices != structTypeArgs.size then
      failed ()
    let ctor ← visitApp' (mkConst ctorVal.name structLvls) structTypeArgs[:structVal.numParams]
    let mut ctorType := ctor.type
    let mut args := #[]
    let mut j := 0
    let mut lastFieldTy : Expr := default
    for i in [:idx+1] do
      unless ctorType.isForall do
        ctorType ← whnf <| ctorType.instantiateRevRange j i args
        j := i
      let .forallE _ dom body _ := ctorType | failed ()
      let dom := dom.instantiateRevRange j i args
      if prop then
        unless ← isProp dom do
          throwError "proj: large elim"
      args := args.push <| Expr.proj structName i struct
      ctorType := body
      lastFieldTy := dom
    lastFieldTy := lastFieldTy.cleanupAnnotations
    return { val := Expr.proj structName idx struct, type := lastFieldTy }

private partial def visit (e : Expr) : M Expr' := do
  withTraceNode `Meta.letToHave.debug (fun res =>
      return m!"{if res.isOk then checkEmoji else crossEmoji} visit{indentExpr e}") do
    match e with
    | .bvar .. => throwError "bvar: unexpected"
    | .fvar .. => visitFVar e
    | .mvar .. => visitMVar e
    | .sort u => return { val := e, type := .sort u.succ }
    | .const constName [] => visitConst e constName []
    | .const constName us => checkMCache e do visitConst e constName us
    | .app .. => checkMCache e do visitApp'' e
    | .lam .. | .forallE .. | .letE .. => checkMCache e do visitBound e
    | .lit v => return { val := e, type := v.type }
    | .mdata _ e' => let e' ← visit e'; return { e' with val := e.updateMData! e' }
    | .proj structName idx struct => checkMCache e do visitProj structName idx (← visit struct)

end

private def main (e : Expr) : MetaM Expr := do
  Prod.fst <$> withTraceNode `Meta.letToHave (fun
      | .ok (_, msg) => pure m!"{checkEmoji} {msg}"
      | .error ex => pure m!"{crossEmoji} {ex.toMessageData}") do
    resetZetaDeltaFVarIds
    withTrackingZetaDelta <|
    withTransparency TransparencyMode.all <|
    withInferTypeConfig do
      let lctx ← instantiateLCtxMVars (← getLCtx)
      withLCtx lctx {} do
        let (e', s) ← visit e |>.run {} |>.run |>.run {}
        if s.count == 0 then
          trace[Meta.letToHave] "result: (no change)"
        else
          trace[Meta.letToHave] "result:{indentExpr e'.val}"
        return (e'.val, m!"transformed {s.count} `let` expressions into `have` expressions")

end LetToHave

/--
Transforms non-dependent `let` expressions into `have` expressions.
If `e` is not type correct, returns `e`.
The `Meta.letToHave` trace class logs errors and messages.
-/
def letToHave (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  LetToHave.main e

builtin_initialize
  registerTraceClass `Meta.letToHave
  registerTraceClass `Meta.letToHave.debug

end Lean.Meta
