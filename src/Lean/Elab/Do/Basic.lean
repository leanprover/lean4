/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Do.InferControlInfo
public import Lean.Elab.Binders
import Lean.Meta.ProdN
public import Lean.Parser
meta import Lean.Parser.Do
import Init.Omega

public section

namespace Lean.Elab.Do

open Lean Meta Parser.Term

builtin_initialize registerTraceClass `Elab.do
builtin_initialize registerTraceClass `Elab.do.match
builtin_initialize registerTraceClass `Elab.do.step

structure MonadInfo where
  /-- The inferred type of the monad of type `Type u → Type v`. -/
  m : Expr
  /-- The `u` in `m : Type u → Type v`. -/
  u : Level
  /-- The `v` in `m : Type u → Type v`. -/
  v : Level
  /-- The cached `PUnit` expression. -/
  cachedPUnit : Expr :=
    if u matches .zero then mkConst ``Unit else mkConst ``PUnit [mkLevelSucc u]
  /-- The cached `PUnit.unit` expression. -/
  cachedPUnitUnit : Expr :=
    if u matches .zero then mkConst ``Unit.unit else mkConst ``PUnit.unit [mkLevelSucc u]

-- Same pattern as for `Methods`/`MethodsRef` in `SimpM`.
private opaque ContInfoRefPointed : NonemptyType.{0}

def ContInfoRef : Type := ContInfoRefPointed.type

instance : Nonempty ContInfoRef :=
  by exact ContInfoRefPointed.property

/-- Whether a code block is alive or dead. -/
inductive CodeLiveness where
  /-- We inferred the code is semantically dead and don't need to elaborate it at all. -/
  | deadSyntactically
  /-- We inferred the code is semantically dead, but we need to elaborate it to produce a program. -/
  | deadSemantically
  /-- The code is alive. (Or it is dead, but we failed to prove it so.)  -/
  | alive

instance : ToString CodeLiveness where
  toString
    | .alive => "alive"
    | .deadSyntactically => "deadSyntactically"
    | .deadSemantically => "deadSemantically"

instance : ToMessageData CodeLiveness where
  toMessageData l := toString l

/-- The least upper bound of two code livenesses. -/
def CodeLiveness.lub (a b : CodeLiveness) : CodeLiveness :=
  match a, b with
  | .alive, _ => .alive
  | _, .alive => .alive
  | .deadSyntactically, _ => b
  | _, .deadSyntactically => a
  | _, _ => a

structure Context where
  /-- Inferred and cached information about the monad. -/
  monadInfo : MonadInfo
  /-- The mutable variables in declaration order. -/
  mutVars : Array Ident := #[]
  /-- Maps mutable variable names to their initial FVarIds. -/
  mutVarDefs : Std.HashMap Name FVarId := {}
  /--
  The expected type of the current `do` block.
  This can be different from `earlyReturnType` in `for` loop `do` blocks, for example.
  -/
  doBlockResultType : Expr
  /-- Information about `return`, `break` and `continue` continuations. -/
  contInfo : ContInfoRef
  /--
  Whether the current `do` element is dead code. `elabDoElem` will emit a warning if not `.alive`.
  -/
  deadCode : CodeLiveness := .alive

abbrev DoElabM := ReaderT Context Term.TermElabM

/--
Whether the continuation of a `do` element is duplicable and if so whether it is just `pure r` for
the result variable `r`. Saying `nonDuplicable` is always safe; `duplicable` allows for more
optimizations.
-/
inductive DoElemContKind
  | nonDuplicable
  | duplicable
  deriving Inhabited

/--
Elaboration of a `do` block `do $e; $rest`, results in a call
``elabTerm `(do $e; $rest) = elabElem e dec``, where `elabElem e ·` is the elaborator for `do`
element `e`, and `dec` is the `DoElemCont` describing the elaboration of the rest of the block
`rest`.

If the semantics of `e` resumes its continuation `rest`, its elaborator must bind its result to
`resultName`, ensure that it has type `resultType` and then elaborate `rest` using `dec`.

Clearly, for term elements `e : m α`, the result has type `α`.
More subtly, for binding elements `let x := e` or `let x ← e`, the result has type `PUnit` and is
unrelated to the type of the bound variable `x`.

Examples:
* `return` drops the continuation; `return x; pure ()` elaborates to `pure x`.
* `let x ← e; rest x` elaborates to `e >>= fun x => rest x`.
* `let x := 3; let y ← (let x ← e); rest x` elaborates to
  `let x := 3; e >>= fun x_1 => let y := (); rest x`, which is immediately zeta-reduced to
  `let x := 3; e >>= fun x_1 => rest x`.
* `one; two` elaborates to `one >>= fun (_ : PUnit) => two`; it is an error if `one` does not have
  type `PUnit`.
-/
structure DoElemCont where
  mk ::
  /-- The name of the monadic result variable. -/
  resultName : Name
  /-- The type of the monadic result. -/
  resultType : Expr
  /--
  The continuation to elaborate the `rest` of the block. It assumes that the result of the `do`
  block is bound to `resultName` with the correct type (that is, `resultType`, potentially refined
  by a dependent `match`).
  -/
  k : DoElabM Expr
  /--
  Whether we are OK with generating the code of the continuation multiple times, e.g. in different
  branches of a `match` or `if`.
  -/
  kind : DoElemContKind := .nonDuplicable
  /-- An optional hint for trace messages. -/
  ref : Syntax := .missing
deriving Inhabited

/--
The type of elaborators for `do` block elements.

It is ``elabTerm `(do $e; $rest) = elabElem e dec``, where `elabElem e ·` is the elaborator for `do`
element `e`, and `dec` is the `DoElemCont` describing the elaboration of the rest of the block
`rest`.
-/
abbrev DoElab := TSyntax `doElem → DoElemCont → DoElabM Expr

structure ReturnCont where
  resultType : Expr
  /--
  The elaborator constructing a jump site to the return continuation,
  given some return value. The type of this return value determines the type of the jump expression;
  this could very well be different than the `resultType` in case an intervening `match` as refined
  `resultType`. So `k` must *not* hardcode the type `resultType` into its definition; rather it
  should infer the type of the return value argument.
  -/
  k : Expr → DoElabM Expr
  deriving Inhabited

/--
Information about a success, `return`, `break` or `continue` continuation that will be filled in
after the code using it has been elaborated.
-/
structure ContInfo where
  returnCont : ReturnCont
  breakCont : Option (DoElabM Expr) := none
  continueCont : Option (DoElabM Expr) := none
deriving Inhabited

unsafe def ContInfo.toContInfoRefImpl (m : ContInfo) : ContInfoRef :=
  unsafeCast m

@[implemented_by ContInfo.toContInfoRefImpl]
opaque ContInfo.toContInfoRef (m : ContInfo) : ContInfoRef

unsafe def ContInfoRef.toContInfoImpl (m : ContInfoRef) : ContInfo :=
  unsafeCast m

@[implemented_by ContInfoRef.toContInfoImpl]
opaque ContInfoRef.toContInfo (m : ContInfoRef) : ContInfo

/-- Constructs `m α` from `α`. -/
def mkMonadicType (resultType : Expr) : DoElabM Expr :=
  return mkApp (← read).monadInfo.m resultType

/-- The cached `PUnit` expression. -/
def mkPUnit : DoElabM Expr := do
  return (← read).monadInfo.cachedPUnit

/-- The cached ``PUnit.unit`` expression. -/
def mkPUnitUnit : DoElabM Expr := do
  return (← read).monadInfo.cachedPUnitUnit

/-- The expression ``pure (α:=α) e``. -/
def mkPureApp (α e : Expr) : DoElabM Expr := do
  let info := (← read).monadInfo
  if (← read).deadCode matches .deadSyntactically then
    -- There is no dead syntax here. Just return a fresh metavariable so that we don't
    -- do the `Term.ensureHasType` check below.
    return ← mkFreshExprMVar (mkApp info.m α)
  let α ← Term.ensureHasType (mkSort (mkLevelSucc info.u)) α
  let e ← Term.ensureHasType α e
  let instPure ← Term.mkInstMVar (mkApp (mkConst ``Pure [info.u, info.v]) info.m)
  let instPure ← instantiateMVars instPure
  return mkApp4 (mkConst ``Pure.pure [info.u, info.v]) info.m instPure α e

/-- Create a `DoElemCont` returning the result using `pure`. -/
def DoElemCont.mkPure (resultType : Expr) : TermElabM DoElemCont := do
  let r ← mkFreshUserName `r
  return {
    resultName := r,
    resultType,
    k := do let decl ← getLocalDeclFromUserName r; mkPureApp decl.type decl.toExpr,
    kind := .duplicable
    ref := .missing
  }

/-- Create a `ReturnCont` returning the result using `pure`. -/
def ReturnCont.mkPure (resultType : Expr) : TermElabM ReturnCont := do
  return { resultType, k x := do
    mkPureApp (← inferType x) x }

/-- The expression ``Bind.bind (α:=α) (β:=β) e k``. -/
def mkBindApp (α β e k : Expr) : DoElabM Expr := do
  let info := (← read).monadInfo
  let α ← Term.ensureHasType (mkSort (mkLevelSucc info.u)) α
  let mα := mkApp info.m α
  let e ← Term.ensureHasType mα e
  let k ← Term.ensureHasType (← mkArrow α (mkApp info.m β)) k
  let instBind ← Term.mkInstMVar (mkApp (mkConst ``Bind [info.u, info.v]) info.m)
  return mkApp6 (mkConst ``Bind.bind [info.u, info.v]) info.m instBind α β e k

/-- Register the given name as that of a `mut` variable. -/
def declareMutVar (x : Ident) (k : DoElabM α) : DoElabM α := do
  let id ← getFVarFromUserName x.getId
  withReader (fun ctx => { ctx with
    mutVars := ctx.mutVars.push x,
    mutVarDefs := ctx.mutVarDefs.insert x.getId id.fvarId!,
  }) k

/-- Register the given names as that of `mut` variables. -/
def declareMutVars (xs : Array Ident) (k : DoElabM α) : DoElabM α := do
  let baseIds ← xs.mapM (getFVarFromUserName ·.getId)
  withReader (fun ctx => { ctx with
    mutVars := ctx.mutVars ++ xs,
    mutVarDefs := ctx.mutVarDefs.insertMany (xs.map (·.getId) |>.zip (baseIds.map (·.fvarId!))),
  }) k

/-- Register the given name as that of a `mut` variable if the syntax token `mut` is present. -/
def declareMutVar? (mutTk? : Option Syntax) (x : Ident) (k : DoElabM α) : DoElabM α :=
  if mutTk?.isSome then declareMutVar x k else k

/-- Register the given names as that of `mut` variables if the syntax token `mut` is present. -/
def declareMutVars? (mutTk? : Option Syntax) (xs : Array Ident) (k : DoElabM α) : DoElabM α :=
  if mutTk?.isSome then declareMutVars xs k else k

/-- Throw an error if the given name is not a declared `mut` variable. -/
def throwUnlessMutVarDeclared (x : Ident) : DoElabM Unit := do
  unless (← read).mutVarDefs.contains x.getId do
    let xName := x.getId.simpMacroScopes
    throwErrorAt x "Variable `{xName}` cannot be mutated. Only variables declared using `let mut` can be mutated.
      If you did not intend to mutate but define `{xName}`, consider using `let {xName}` instead"

/-- Throw an error if the given names are not declared `mut` variables. -/
def throwUnlessMutVarsDeclared (xs : Array Ident) : DoElabM Unit := do
  for x in xs do throwUnlessMutVarDeclared x

/-- Throw an error if a declaration of the given name would shadow a `mut` variable. -/
def checkMutVarsForShadowingOne (x : Ident) : DoElabM Unit := do
  if (← read).mutVarDefs.contains x.getId then
    throwErrorAt x "mutable variable `{x.getId.simpMacroScopes}` cannot be shadowed"

/-- Throw an error if a declaration of the given name would shadow a `mut` variable. -/
def checkMutVarsForShadowing (xs : Array Ident) : DoElabM Unit := do
  for x in xs do checkMutVarsForShadowingOne x

/-- Create a fresh `α` that would fit in `m α`. -/
def mkFreshResultType (userName := `α) (kind := MetavarKind.natural) : DoElabM Expr := do
  mkFreshExprMVar (mkSort (mkLevelSucc (← read).monadInfo.u)) (userName := userName) (kind := kind)

/--
Like `controlAt TermElabM`, but it maintains the state using the `DoElabM`'s ref cell instead of returning it
in the `TermElabM` result. This makes it possible to run multiple `DoElabM` computations in a row.
-/
@[inline]
def controlAtTermElabM (k : (runInBase : ∀ {β}, DoElabM β → TermElabM β) → TermElabM α) : DoElabM α := fun ctx => do
  k (· ctx)

@[inline]
def mapTermElabM (f : ∀{α}, TermElabM α → TermElabM α) {α} (k : DoElabM α) : DoElabM α :=
  controlAtTermElabM fun runInBase => f (runInBase <| k)

@[inline]
def map1TermElabM (f : ∀{α}, (β → TermElabM α) → TermElabM α) {α} (k : β → DoElabM α) : DoElabM α :=
  controlAtTermElabM fun runInBase => f fun b => runInBase <| k b

def withDeadCode (deadCode : CodeLiveness) (k : DoElabM α) : DoElabM α := do
  withReader (fun ctx => { ctx with deadCode }) k

/--
The subset of `mutVars` that were reassigned in any of the `childCtxs` relative to the given
`rootCtx`.
-/
def getReassignedMutVars (rootCtx : LocalContext) (mutVars : Std.HashSet Name) (childCtxs : Array LocalContext) : Std.HashSet Name := Id.run do
  let mut reassignedMutVars := Std.HashSet.emptyWithCapacity mutVars.size
  for childCtx in childCtxs do
    let newDefs := childCtx.findFromUserNames mutVars.inner (start := rootCtx.numIndices)
    reassignedMutVars := reassignedMutVars.insertMany (newDefs.map (·.userName))
  return reassignedMutVars

/--
Adds the new reaching definitions of the given `tunneledVars` in `childCtx` relative to `rootCtx` as
non-dependent decls.
-/
def addReachingDefsAsNonDep (rootCtx childCtx : LocalContext) (tunneledVars : Std.HashMap Name α) : MetaM LocalContext := do
  -- let ldeclToUserNameAndFVarId (d : LocalDecl) := (d.userName, d.fvarId.name)
  -- let lctxToMessage (lctx : LocalContext) := toMessageData <| lctx.decls.toList.filterMap (ldeclToUserNameAndFVarId <$> ·)
  -- trace[Elab.do] "addReachingDefsAsNonDep\nTunnel vars: {tunneledVars.toList.map Prod.fst}\nRoot ctx: {lctxToMessage rootCtx}\nChild ctx: {lctxToMessage childCtx}"
  let mut tunnelDecls := childCtx.findFromUserNames tunneledVars (start := rootCtx.numIndices)
  -- We must also tunnel any variables that the tunneled vars depend on; hence compute the closure.
  let fvars ← (·.2.fvarIds) <$> (tunnelDecls.mapM (Expr.collectFVars ·.type) |>.run {})
  let fvarDecls ← fvars.mapM (·.getDecl)
  let fvarDecls := fvarDecls.insertionSort (·.index > ·.index)
    |>.takeWhile (·.index >= rootCtx.numIndices)
    |>.reverse
  -- trace[Elab.do] "addReachingDefsAsNonDep: {fvarDecls.map (·.toExpr)}, {tunnelDecls.map (·.toExpr)}"
  tunnelDecls := tunnelDecls.filter fun tun => !fvarDecls.any (·.index == tun.index)
  tunnelDecls := fvarDecls ++ tunnelDecls
  let mut rootCtx := rootCtx
  for decl in tunnelDecls do
    rootCtx := rootCtx.addDecl (decl.setNondep true)
  return rootCtx

/--
Restores the local context to `oldCtx` and adds the new reaching definitions of the mut vars and
result. Then resume the continuation `k` with the `mutVars` restored to the given `oldMutVars`.

This function is useful to de-nest
```
let mut x := 0
let y := 3
let z ← do
  let mut y ← e
  x := y + 1
  pure y
let y := y + 3
pure (x + y + z)
```
into
```
let mut x := 0
let y := 3
let mut y† ← e
x := y† + 1
let z ← pure y†
let y := y + 3
pure (x + y + z)
```
Note that the continuation of the `let z ← ...` bind, roughly
``k := .cont `z _ `(let y := y + 3; pure (x + y + z))``,
needs to elaborated in a local context that contains the reassignment of `x`, but not the shadowing
mut var definition of `y`.
-/
def withLCtxKeepingMutVarDefs (oldLCtx : LocalContext) (oldCtx : Context) (resultName : Name) (k : DoElabM α) : DoElabM α := do
  let oldMutVars := oldCtx.mutVars
  let oldMutVarDefs := oldCtx.mutVarDefs
  let tunneledDefs := oldMutVarDefs.insert resultName ⟨`unused⟩  -- tunneledDefs is used as a set, so the FVarId doesn't matter
  let newCtx ← addReachingDefsAsNonDep oldLCtx (← getLCtx) tunneledDefs
  withLCtx' newCtx <| withReader (fun ctx => { ctx with
    mutVars := oldMutVars,
    mutVarDefs := oldMutVarDefs
  }) k

/--
Return `$e >>= fun ($dec.resultName : $dec.resultType) => $(← dec.k)`, cancelling
the bind if `$(← dec.k)` is `pure $dec.resultName` or `e` is some `pure` computation.
-/
def DoElemCont.mkBindUnlessPure (dec : DoElemCont) (e : Expr) : DoElabM Expr := do
  let x := dec.resultName
  let eResultTy := dec.resultType
  let k := dec.k
  -- The .ofBinderName below is mainly to interpret `__do_lift` binders as implementation details.
  let declKind := .ofBinderName x
  withRef? dec.ref do
  withLocalDecl x .default eResultTy (kind := declKind) fun xFVar => do
    let body ← k
    let body' := body.consumeMData
    -- First try to contract `e >>= pure` into `e`.
    -- Reason: for `pure e >>= pure`, we want to get `pure e` and not `have xFVar := e; pure xFVar`.
    if body'.isAppOfArity ``Pure.pure 4 && body'.getArg! 3 == xFVar then
      let body'' ← mkPureApp eResultTy xFVar
      if ← withNewMCtxDepth do isDefEq body' body'' then
        return e

    -- Now test whether we can contract `pure e >>= k` into `have xFVar := e; k xFVar`. We zeta `xFVar` when
    -- `e` is duplicable; we don't look at `k` to see whether it is used at most once.
    let e' := e.consumeMData
    if e'.isAppOfArity ``Pure.pure 4 then
      let eRes := e'.getArg! 3
      let e' ← mkPureApp eResultTy eRes
      let (isPure, isDuplicable) ← withNewMCtxDepth do
        let isPure ← isDefEq e e'
        let isDuplicable ← isDefEq eResultTy (← mkPUnit)
          -- <||> pure eRes.isFVar -- this is too aggressive; users expect to see "useless binds" after elaboration
        return (isPure, isDuplicable)
      if isPure then
        if isDuplicable then
          return ← mapLetDeclZeta (nondep := true) (kind := declKind) x eResultTy eRes fun _ => k
        -- else -- would be too aggressive
        --   return ← mapLetDecl (nondep := true) (kind := declKind) x eResultTy eRes fun _ => k ref

    let kResultTy ← mkFreshResultType `kResultTy
    let body ← Term.ensureHasType (← mkMonadicType kResultTy) body
    let k ← mkLambdaFVars #[xFVar] body
    mkBindApp eResultTy kResultTy e k

/--
Return `let $k.resultName : PUnit := PUnit.unit; $(← k.k)`, ensuring that the result type of `k.k`
is `PUnit` and then immediately zeta-reduce the `let`.
-/
def DoElemCont.continueWithUnit (dec : DoElemCont) : DoElabM Expr := do
  let unit ← mkPUnitUnit
  discard <| Term.ensureHasType dec.resultType unit
  mapLetDeclZeta dec.resultName (← mkPUnit) unit (nondep := true) (kind := .ofBinderName dec.resultName) fun _ =>
    withRef? dec.ref dec.k

/-- Elaborate the `DoElemCont` with the `deadCode` flag set to `deadSyntactically` to emit warnings. -/
def DoElemCont.elabAsSyntacticallyDeadCode (dec : DoElemCont) : DoElabM Unit :=
  withNewMCtxDepth do
  withDeadCode .deadSyntactically do
  withLocalDecl dec.resultName .default (← mkFreshResultType) (kind := .implDetail) fun _ => do
    let s ← Term.saveState
    let log ← Core.getAndEmptyMessageLog
    try discard <| dec.k catch _ => pure ()
    let warnings := MessageLog.getWarningMessages (← Core.getMessageLog)
    s.restore
    Core.setMessageLog (log ++ warnings)

/--
Given a list of mut vars `vars` and an FVar `tupleVar` binding a tuple, bind the mut vars to the
fields of the tuple and call `k` in the resulting local context.
-/
def bindMutVarsFromTuple (vars : List Name) (tupleVar : FVarId) (k : DoElabM Expr) : DoElabM Expr :=
  do go vars tupleVar (← tupleVar.getType) #[]
where
  go vars tupleVar tupleTy letFVars := do
    let tuple := mkFVar tupleVar
    match vars with
    | []  => mkLetFVars letFVars (← k)
    | [x] =>
      withLetDecl x tupleTy tuple fun x => do mkLetFVars (letFVars.push x) (← k)
    | [x, y] =>
      let (fst, fstTy, snd, sndTy) ← getProdFields tuple tupleTy
      withLetDecl x fstTy fst fun x =>
      withLetDecl y sndTy snd fun y => do mkLetFVars (letFVars.push x |>.push y) (← k)
    | x :: xs => do
      let (fst, fstTy, snd, sndTy) ← getProdFields tuple tupleTy
      withLetDecl x fstTy fst fun x => do
      withLetDecl (← tupleVar.getUserName) sndTy snd fun r => do
        go xs r.fvarId! sndTy (letFVars |>.push x |>.push r)

private def withLambda (name : Name) (type : Expr) (k : Expr → DoElabM Expr) (kind := LocalDeclKind.default) (bi := BinderInfo.default) : DoElabM Expr := do
  withLocalDecl name type (bi := bi) (kind := kind) fun r => do
    mkLambdaFVars #[r] (← k r)

private def withLambdaIf (b : Bool) (name : Name) (type : Expr) (k : DoElabM Expr) (kind := LocalDeclKind.default) (bi := BinderInfo.default) : DoElabM Expr := do
  if b then withLambda name type (fun _ => k) kind bi else k

/--
  Backtrackable state for the `TermElabM` monad.
-/
structure SavedState where
  «term» : Term.SavedState
  deriving Nonempty

def SavedState.restore (s : SavedState) (restoreInfo : Bool := false) : DoElabM Unit := do
  s.term.restore (restoreInfo := restoreInfo)

protected def DoElabM.saveState : DoElabM SavedState :=
  return { «term» := (← Term.saveState) }

instance : MonadBacktrack SavedState DoElabM where
  saveState      := DoElabM.saveState
  restoreState b := b.restore

def observingPostpone (x : DoElabM α) : DoElabM (Option α) := do
  let s ← saveState
  try
    some <$> x
  catch ex => match ex with
    | .error .. => throw ex
    | .internal id _ =>
      if id == postponeExceptionId then
        s.restore
        pure none
      else
        throw ex

def doElabToSyntaxWithExpectedType (hint : MessageData) (doElab : Option Expr → DoElabM Expr) (k : Term → DoElabM α) (ref : Syntax := .missing) : DoElabM α :=
  controlAtTermElabM fun runInBase =>
    Term.elabToSyntax (hint? := hint) (ref := ref)
      (fun ty? => runInBase (doElab ty?)) (runInBase ∘ k)

def doElabToSyntax (hint : MessageData) (doElab : DoElabM Expr) (k : Term → DoElabM α) (ref : Syntax := .missing) : DoElabM α :=
  doElabToSyntaxWithExpectedType hint (fun _ty? => doElab) k ref

/--
Call `caller` with a duplicable proxy of `dec`.
When the proxy is elaborated more than once, a join point is introduced so that `dec` is only
elaborated once to fill in the RHS of this join point.

This is useful for control-flow constructs like `if` and `match`, where multiple tail-called
branches share the continuation.
-/
def DoElemCont.withDuplicableCont (nondupDec : DoElemCont) (callerInfo : ControlInfo) (caller : DoElemCont → DoElabM Expr) : DoElabM Expr := do
  if nondupDec.kind matches .duplicable .. then
    return ← caller nondupDec
  let γ := (← read).doBlockResultType
  let mγ ← mkMonadicType γ
  let mutVars := (← read).mutVars |>.filter (callerInfo.reassigns.contains ·.getId)
  let mutVarNames := mutVars.map (·.getId)
  let joinName ← mkFreshUserName `__do_jp
  -- σ is the tuple type of the mut vars, or mγ if jumpCount = 0. Hence it is either level mi.u or mi.v.
  -- let σ ← mkFreshTypeMVar (userName := `σ)
  let mutDecls ← mutVarNames.mapM (getLocalDeclFromUserName ·)
  let mutTypes := mutDecls.map (·.type)
  let joinTy ← mkArrow nondupDec.resultType (← mkArrowN mutTypes mγ)
  let joinRhsMVar ← mkFreshExprSyntheticOpaqueMVar joinTy
  withLetDecl joinName joinTy joinRhsMVar (kind := .implDetail) (nondep := true) fun jp => do
  let mkJump : DoElabM Expr := do
    let jp' ← getFVarFromUserName joinName
    let result ← getFVarFromUserName nondupDec.resultName
    let mut e := mkApp jp' result
    for x in mutVars do
      let newX ← getFVarFromUserName x.getId
      Term.addTermInfo' x newX
      e := mkApp e (← getFVarFromUserName x.getId)
    return e

  let elabBody :=
    caller { nondupDec with k := mkJump, kind := .duplicable }

  -- We need observingPostpone to decouple elaboration problems from the RHS and the body.
  let body? : Option Expr ← observingPostpone elabBody

  let joinRhs ← joinRhsMVar.mvarId!.withContext do
    withLocalDeclD nondupDec.resultName nondupDec.resultType fun r => do
    withLocalDeclsDND (mutDecls.map fun (d : LocalDecl) => (d.userName, d.type)) fun muts => do
    for (x, newX) in mutVars.zip muts do Term.addTermInfo' x newX
    withDeadCode (if callerInfo.exitsRegularly then .alive else .deadSemantically) do
    let e ← nondupDec.k
    mkLambdaFVars (#[r] ++ muts) e
  discard <| joinRhsMVar.mvarId!.checkedAssign joinRhs

  let body ← body?.getDM do
    -- Here we unconditionally add a pending MVar.
    doElabToSyntax "join point RHS" elabBody (Term.postponeElabTerm · mγ)

  mkLetFVars (generalizeNondepLet := false) #[jp] body

/--
Create syntax standing in for an unelaborated metavariable.
After the syntax has been elaborated, the `DoElabM MVarId` can be used to get the metavariable.
-/
def mkSyntheticHole (ref : Syntax) : MetaM (Term × MetaM MVarId) := withFreshMacroScope do
  let name ← Term.mkFreshIdent ref
  let result ← `(?$name)
  let getMVar : MetaM MVarId := do
    let some mvar := (← getMCtx).findUserName? name.getId
      | throwError "Internal error: could not find metavariable {`m}. Has the syntax {result} been elaborated yet?"
    return mvar
  return (result, getMVar)

def getReturnCont : DoElabM ReturnCont := do
  return (← read).contInfo.toContInfo.returnCont

def getBreakCont : DoElabM (Option (DoElabM Expr)) := do
  return (← read).contInfo.toContInfo.breakCont

def getContinueCont : DoElabM (Option (DoElabM Expr)) := do
  return (← read).contInfo.toContInfo.continueCont

/--
Prepare the context for elaborating the body of a loop.
This includes setting the return continuation, break continuation, continue continuation, as
well as the changed result type of the `do` block in the loop body.
-/
def enterLoopBody (breakCont continueCont : DoElabM Expr) (returnCont : ReturnCont) (body : DoElabM α) : DoElabM α := do
  let contInfo := { (← read).contInfo.toContInfo with returnCont, breakCont, continueCont }.toContInfoRef
  withReader (fun ctx => { ctx with contInfo }) body

/--
Prepare the context for elaborating the body of a `do` block that does not support `mut` vars,
`break`, `continue` or `return`.
-/
def withoutControl (k : DoElabM Expr) : DoElabM Expr := do
  let error := throwError "This `do` block does not support `break`, `continue` or `return`."
  let rc ← getReturnCont
  let contInfo := { breakCont := error, continueCont := error, returnCont := { rc with k _ := error }}
  let contInfo := ContInfo.toContInfoRef contInfo
  withReader (fun ctx => { ctx with contInfo }) k

/-- Set the new `do` block result type for the scope of the continuation `k`. -/
@[inline]
def withDoBlockResultType (doBlockResultType : Expr) (k : DoElabM α) : DoElabM α := do
  withReader (fun ctx => { ctx with doBlockResultType }) k

/--
Prepare the context for elaborating the body of a `finally` block.
There is no support for `mut` vars, `break`, `continue` or `return` in a `finally` block.
-/
def enterFinally (resultType : Expr) (k : DoElabM Expr) : DoElabM Expr := do
  withoutControl do
  withDoBlockResultType resultType k

/-- Extracts `MonadInfo` and monadic result type `α` from the expected type of a `do` block `m α`. -/
private partial def extractMonadInfo (expectedType? : Option Expr) : Term.TermElabM (MonadInfo × Expr) := do
  let some expectedType := expectedType? | mkUnknownMonadResult
  let extractStep? (type : Expr) : Term.TermElabM (Option (MonadInfo × Expr)) := do
    let .app m resultType := type.consumeMData | return none
    unless ← isType resultType do return none
    let u ← getDecLevel resultType
    let v ← getDecLevel type
    let u := u.normalize
    let v := v.normalize
    return some ({ m, u, v }, resultType)
  let rec extract? (type : Expr) : Term.TermElabM (Option (MonadInfo × Expr)) := do
    match (← extractStep? type) with
    | some r => return r
    | none =>
      let typeNew ← whnfCore type
      if typeNew != type then
        extract? typeNew
      else
        if typeNew.getAppFn.isMVar then
          mkUnknownMonadResult
        else match (← unfoldDefinition? typeNew) with
          | some typeNew => extract? typeNew
          | none => return none
  match (← extract? expectedType) with
  | some r => return r
  | none   => throwError "invalid `do` notation, expected type is not a monad application{indentExpr expectedType}\nYou can use the `do` notation in pure code by writing `Id.run do` instead of `do`, where `Id` is the identity monad."
where
  mkUnknownMonadResult : TermElabM (MonadInfo × Expr) := do
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let m ← mkFreshExprMVar (← mkArrow (mkSort (mkLevelSucc u)) (mkSort (mkLevelSucc v))) (userName := `m)
    let resultType ← mkFreshExprMVar (mkSort (mkLevelSucc u)) (userName := `α)
    return ({ m, u, v }, resultType)

/-- Create the `Context` for `do` elaboration from the given expected type of a `do` block. -/
def mkContext (expectedType? : Option Expr) : TermElabM Context := do
  let (mi, resultType) ← extractMonadInfo expectedType?
  let returnCont ← ReturnCont.mkPure resultType
  let contInfo := ContInfo.toContInfoRef { returnCont }
  return { monadInfo := mi, doBlockResultType := resultType, contInfo }

section NestedActions

-- @[builtin_term_elab liftMethod]
def elabNestedAction : Term.TermElab := fun stx _ty? => do
  let `(← $_rhs) := stx | throwUnsupportedSyntax
  throwErrorAt stx "Nested action `{stx}` must be nested inside a `do` expression."

/-- Return true if we should not lift nested action `(← …)` out of syntax nodes with the given kind. -/
private def liftNestedActionDelimiter (k : SyntaxNodeKind) : Bool :=
  k == ``Parser.Term.do ||
  k == ``Parser.Term.doSeqIndent ||
  k == ``Parser.Term.doSeqBracketed ||
  k == ``Parser.Term.termReturn ||
  k == ``Parser.Term.termUnless ||
  k == ``Parser.Term.termTry ||
  k == ``Parser.Term.termFor

private def letDeclArgHasBinders (letDeclArg : Syntax) : Bool :=
  let k := letDeclArg.getKind
  if k == ``Parser.Term.letPatDecl then
    false
  else if k == ``Parser.Term.letEqnsDecl then
    true
  else if k == ``Parser.Term.letIdDecl then
    -- letIdLhs := letId >> many (ppSpace >> letIdBinder) >> optType
    let binders := letDeclArg[1]
    binders.getNumArgs > 0
  else
    false

/-- Return `true` if the given `letDecl` contains binders. -/
private def letDeclHasBinders (letDecl : Syntax) : Bool :=
  letDeclArgHasBinders letDecl[0]

/-- Return true if we should generate an error message when lifting a method over this kind of syntax. -/
private def liftMethodForbiddenBinder (stx : Syntax) : Bool :=
  let k := stx.getKind
  -- TODO: make this extensible in the future.
  if k == ``Parser.Term.fun || k == ``Parser.Term.matchAlts ||
     k == ``Parser.Term.doLetRec || k == ``Parser.Term.letrec then
     -- It is never ok to lift over this kind of binder
    true
  -- The following kinds of `let`-expressions require extra checks to decide whether they contain binders or not
  else if k == ``Parser.Term.letDecl then
    letDeclHasBinders stx
  else
    false

-- TODO: we must track whether we are inside a quotation or not.
private partial def hasNestedActionsToLift : Syntax → Bool
  | Syntax.node _ k args =>
    if liftNestedActionDelimiter k then false
    -- NOTE: We don't check for lifts in quotations here, which doesn't break anything but merely makes this rare case a
    -- bit slower
    else if k == ``Parser.Term.liftMethod then true
    -- For `pure` if-then-else, we only lift `(<- ...)` occurring in the condition.
    else if k == ``termDepIfThenElse || k == ``termIfThenElse then args.size >= 2 && hasNestedActionsToLift args[1]!
    else args.any hasNestedActionsToLift
  | _ => false

private partial def expandNestedActionsAux (baseId : Name) (inQuot : Bool) (inBinder : Bool) : Syntax → StateT (Array (TSyntax `doElem)) DoElabM Syntax
  | stx@(Syntax.node i k args) =>
    if k == choiceKind then do
      -- choice node: check that lifts are consistent
      let alts ← stx.getArgs.mapM (expandNestedActionsAux baseId inQuot inBinder · |>.run #[])
      let (_, lifts) := alts[0]!
      unless alts.all (·.2 == lifts) do
        throwErrorAt stx "Cannot lift nested action `{stx}` over inconsistent syntax variants.\nConsider lifting out the binding manually."
      modify (· ++ lifts)
      return .node i k (alts.map (·.1))
    else if liftNestedActionDelimiter k then
      return stx
    -- For `pure` if-then-else, we only lift `(<- ...)` occurring in the condition.
    else if h : args.size >= 2 ∧ (k == ``termDepIfThenElse || k == ``termIfThenElse) then do
      let inAntiquot := stx.isAntiquot && !stx.isEscapedAntiquot
      let arg1 ← expandNestedActionsAux baseId (inQuot && !inAntiquot || stx.isQuot) inBinder args[1]
      let args := args.set! 1 arg1
      return Syntax.node i k args
    else if k == ``Parser.Term.liftMethod && !inQuot then withFreshMacroScope do
      if inBinder then
        throwErrorAt stx "Cannot lift nested action `{stx}` over a binder.\nThis error usually happens when you are trying to lift a method nested in a `fun`, `let`, or `match`-alternative, and it can often be fixed by adding a missing `do`."
      let term := args[1]!
      let term ← expandNestedActionsAux baseId inQuot inBinder term
      -- keep name deterministic across choice branches
      let id ← mkIdentFromRef (.num baseId (← get).size)
      let auxDoElem ← `(doElem| let $id:ident ← $(⟨term⟩):term)
      modify fun s => s.push auxDoElem
      return id
    else do
      let inAntiquot := stx.isAntiquot && !stx.isEscapedAntiquot
      let inBinder   := inBinder || (!inQuot && liftMethodForbiddenBinder stx)
      let args ← args.mapM (expandNestedActionsAux baseId (inQuot && !inAntiquot || stx.isQuot) inBinder)
      return Syntax.node i k args
  | stx => return stx

def expandNestedActions (stx : TSyntax kind) : DoElabM (Array (TSyntax `doElem) × TSyntax kind) := do
  if !hasNestedActionsToLift stx then
    return (#[], stx)
  else
    let baseId ← withFreshMacroScope (MonadQuotation.addMacroScope `__do_lift)
    let (stx, doElemsNew) ← (expandNestedActionsAux baseId false false stx).run #[]
    return (doElemsNew, ⟨stx⟩)

end NestedActions

unsafe def mkDoElemElabAttributeUnsafe (ref : Name) : IO (KeyedDeclsAttribute DoElab) :=
  mkElabAttribute DoElab `builtin_doElem_elab `doElem_elab `Lean.Parser.Term.doElem ``Lean.Elab.Do.DoElab "do element" ref

@[implemented_by mkDoElemElabAttributeUnsafe]
opaque mkDoElemElabAttribute (ref : Name) : IO (KeyedDeclsAttribute DoElab)

/--
Registers a `do` element elaborator for the given syntax node kind.

A `do` element elaborator should have type `DoElab` (which is
`Lean.Syntax → DoElemCont → DoElabM Expr`), i.e. should take syntax of the given syntax node kind
and a `DoElemCont` as parameters and produce an expression.

When elaborating a `do` block `do e; rest`, the elaborator for `e` is invoked with the syntax of `e`
and the `DoElemCont` representing `rest`.

The `elab_rules` and `elab` commands should usually be preferred over using this attribute
directly.
-/
@[builtin_doc]
builtin_initialize doElemElabAttribute : KeyedDeclsAttribute DoElab ← mkDoElemElabAttribute decl_name%

/--
An auxiliary syntax node expressing that a `doElem` has no nested actions to lift.
This purely to make lifting nested actions more efficient.
-/
def doElemNoNestedAction : Lean.Parser.Parser := leading_parser
  Lean.Parser.doElemParser

builtin_initialize Lean.Parser.registerBuiltinNodeKind ``doElemNoNestedAction

private def withTermInfoContext' (elaborator : Name) (stx : Syntax) (expectedType : Expr) (x : DoElabM Expr) : DoElabM Expr :=
  controlAtTermElabM fun runInBase =>
    Term.withTermInfoContext' elaborator stx (expectedType? := expectedType) (runInBase x)

private def elabDoElemFns (stx : TSyntax `doElem) (cont : DoElemCont)
    (fns : List (KeyedDeclsAttribute.AttributeEntry DoElab)) (catchExPostpone : Bool := true) : DoElabM Expr := do
  let s ← saveState
  match fns with
  | [] => throwError "unexpected `do` element syntax{indentD stx}"
  | elabFn :: elabFns =>
    let expectedType ← mkMonadicType (← read).doBlockResultType
    withTermInfoContext' elabFn.declName stx (expectedType := expectedType) do
      try
        elabFn.value stx cont
      catch ex => match ex with
        | .internal id _ =>
          if id == unsupportedSyntaxExceptionId then
            s.restore
            elabDoElemFns stx cont elabFns
          else if catchExPostpone && id == postponeExceptionId then
            s.restore
            doElabToSyntax m!"do element {stx}" (elabFn.value stx cont) (Term.postponeElabTerm · expectedType)
          else
            throw ex
        | _ => throw ex

private def DoElemCont.mkUnit (ref : Syntax) (k : DoElabM Expr) : DoElabM DoElemCont := do
  let unit ← mkPUnit
  let r ← mkFreshUserName `__r
  return DoElemCont.mk r unit k .nonDuplicable ref

mutual
partial def elabDoElem (stx : TSyntax `doElem) (cont : DoElemCont) (catchExPostpone : Bool := true) : DoElabM Expr := do
  let k := stx.raw.getKind
  trace[Elab.do.step] "do element: {stx}"
  checkSystem "do element elaborator"
  profileitM Exception "do element elaborator" (decl := k) (← getOptions) <|
  withRef stx <| withIncRecDepth <| withFreshMacroScope <| do
  let mγ ← mkMonadicType (← read).doBlockResultType
  if (← read).deadCode matches .deadSyntactically then
    logWarningAt stx "This `do` element and its control-flow region are dead code. Consider removing it."
    return ← mkFreshExprMVar mγ (userName := `deadCode)
  if (← read).deadCode matches .deadSemantically then
    logWarningAt stx "This `do` element and its control-flow region are dead code. Consider refactoring your code to remove it."
  withDeadCode .alive do -- we have warned for this doElem. No need to warn for every element of the block
  let env ← getEnv
  if let some (decl, stxNew?) ← liftMacroM (expandMacroImpl? env stx) then
    let stxNew ← liftMacroM <| liftExcept stxNew?
    return ← withTermInfoContext' decl stx mγ <|
      Term.withMacroExpansion stx stxNew <|
        withRef stxNew <| elabDoElem ⟨stxNew⟩ cont

  let (doElems, stx) ← expandNestedActions stx
  if !doElems.isEmpty then
    return ← elabDoElems1 (doElems.push stx) cont

  match doElemElabAttribute.getEntries (← getEnv) k with
  | []      => throwError "elaboration function for `{k}` has not been implemented{indentD stx}"
  | elabFns => elabDoElemFns stx cont elabFns catchExPostpone

partial def elabDoElems1 (doElems : Array (TSyntax `doElem)) (cont : DoElemCont) (catchExPostpone : Bool := true) : DoElabM Expr := do
  if h : doElems.size = 0 then
    throwError "Empty array of `do` elements passed to `elabDoElems1`."
  else
  let back := doElems.back
  let initCont ← DoElemCont.mkUnit .missing (fun _ => throwError "always replaced")
  let mkCont el k := { initCont with ref := el, k }
  let init := (back, elabDoElem back cont catchExPostpone)
  let (_, res) := doElems.pop.foldr (init := init) fun el (prev, k) =>
    (el, elabDoElem el (mkCont prev k) catchExPostpone)
  res
end

partial def elabDoSeq (doSeq : TSyntax ``doSeq) (cont : DoElemCont) (catchExPostpone : Bool := true) : DoElabM Expr := do
  let s ← saveState
  try
    elabDoElems1 (getDoElems doSeq) cont catchExPostpone
  catch ex => match ex with
    | .internal id _ =>
      if catchExPostpone && id == postponeExceptionId then
        s.restore
        let expectedType ← mkMonadicType (← read).doBlockResultType
        doElabToSyntax m!"do sequence {doSeq}" (elabDoSeq doSeq cont) (Term.postponeElabTerm · expectedType)
      else
        throw ex
    | _ => throw ex

@[builtin_doElem_elab doElemNoNestedAction] def elabDoElemNoNestedAction : DoElab := fun stx cont => do
  let `(doElemNoNestedAction| $e:doElem) := stx | throwUnsupportedSyntax
  elabDoElem e cont

-- @[builtin_term_elab «do»] -- once the legacy `do` elaborator has been phased out
def elabDo : Term.TermElab := fun e expectedType? => do
  let `(do $doSeq) := e | throwError "unexpected `do` block syntax{indentD e}"
  Term.tryPostponeIfNoneOrMVar expectedType?
  let ctx ← mkContext expectedType?
  let cont ← DoElemCont.mkPure ctx.doBlockResultType
  let res ← elabDoSeq doSeq cont |>.run ctx
  -- Synthesizing default instances here is harmful for expressions such as
  -- ```
  -- withTraceNode `Meta.Tactic.solveByElim (return m!"{exceptEmoji ·} trying to apply: {e}") do
  --   ... (g.apply e cfg) ...
  -- ```
  -- Doing so will default the type of `e` to `MessageData` as part of elaborating the `return`
  -- expression before elaboration can propagate that `e : Expr` in the `apply` call.
  -- Term.synthesizeSyntheticMVarsUsingDefault
  trace[Elab.do] "{← instantiateMVars res}"
  pure res
