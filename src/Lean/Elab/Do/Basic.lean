/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Term.TermElabM
public import Lean.Elab.Binders
import Lean.Meta.ProdN
public import Lean.Parser
meta import Lean.Parser.Do

public section

namespace Lean.Elab.Do

open Lean Meta

builtin_initialize registerTraceClass `Elab.do
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
  Whether the current `do` element is dead code. `elabDoElem` will emit a warning if this is `true`.
  -/
  deadCode : Bool := false

structure MonadInstanceCache where
  /-- The inferred `Pure` instance of `(← read).monadInfo.m`. -/
  instPure : Option Expr := none
  /-- The inferred `Bind` instance of `(← read).monadInfo.m`. -/
  instBind : Option Expr := none
  /-- The cached `Pure.pure` expression. -/
  cachedPure : Option Expr := none
  /-- The cached `Bind.bind` expression. -/
  cachedBind : Option Expr := none
  deriving Nonempty

/--
A continuation metavariable.

When generating jumps to join points or filling in expressions for `break` or `continue`, it is
still unclear what mutable variables need to be passed, because it depends on which mutable
variables were reassigned in the control flow path to *any* of the jumps.

The mechanism of `ContVarId` allows to delay the assignment of the jump expressions until the local
contexts of all the jumps are known.
-/
structure ContVarId where
  name : Name
  deriving Inhabited, BEq, Hashable

/--
Information about a jump site associated to `ContVarId`.
There will be one instance per jump site to a join point, or for each `break` or `continue`
element.
-/
structure ContVarJump where
  /--
  The metavariable to be assigned with the jump to the join point.
  Conveniently, its captured local context is that of the jump, in which the new mutable variable
  definitions and result variable are in scope.
  -/
  mvar : Expr
  /-- A reference for error reporting. -/
  ref : Syntax

/--
Information about a `ContVarId`.
-/
structure ContVarInfo where
  /-- The monadic type of the continuation. -/
  type : Expr
  /--
  A superset of the local variable names that the jumps will refer to. Often the `mut` variables.
  Any `let`-bound FV will be turned into a `have`-bound FV by setting their `nondep` flag in the
  local context of the metavariable for the jump site. This is a technicality to ensure that
  `isDefEq` will not inline the `let`s.
  -/
  tunneledVars : Std.HashSet Name
  /-- Local context at the time the continuation variable was created. -/
  lctx : LocalContext
  /-- The tracked jumps to the continuation. Each contains a metavariable to be assigned later. -/
  jumps : Array ContVarJump

structure State where
  monadInstanceCache : MonadInstanceCache := {}
  contVars : Std.HashMap ContVarId ContVarInfo := {}
  deriving Nonempty

abbrev DoElabM := ReaderT Context <| StateRefT State Term.TermElabM

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
  /-- The continuation to elaborate the `rest` of the block. -/
  k : DoElabM Expr
  /--
  Whether we are OK with generating the code of the continuation multiple times, e.g. in different
  branches of a `match` or `if`.
  -/
  kind : DoElemContKind := .nonDuplicable
  /-- An optional hint for trace messages. -/
  ref : Syntax := .missing
  /-- How `resultName` should be introduced. Useful to say `.implDetail`. -/
  declKind : LocalDeclKind := .default
deriving Inhabited

/--
The type of elaborators for `do` block elements.

It is ``elabTerm `(do $e; $rest) = elabElem e dec``, where `elabElem e ·` is the elaborator for `do`
element `e`, and `dec` is the `DoElemCont` describing the elaboration of the rest of the block
`rest`.
-/
abbrev DoElab := TSyntax `doElem → DoElemCont → DoElabM Expr

/--
Information about a success, `return`, `break` or `continue` continuation that will be filled in
after the code using it has been elaborated.
-/
structure ContInfo where
  returnCont : DoElemCont
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
def mkMonadicType (resultType : Expr) : DoElabM Expr := do
  return mkApp (← read).monadInfo.m resultType

/-- The cached `PUnit` expression. -/
def mkPUnit : DoElabM Expr := do
  return (← read).monadInfo.cachedPUnit

/-- The cached ``PUnit.unit`` expression. -/
def mkPUnitUnit : DoElabM Expr := do
  return (← read).monadInfo.cachedPUnitUnit

/-- The cached `@Pure.pure m instPure` expression. -/
private def getCachedPure : DoElabM Expr := do
  let s ← get
  if let some cachedPure := s.monadInstanceCache.cachedPure then return cachedPure
  let info := (← read).monadInfo
  let instPure ← Term.mkInstMVar (mkApp (mkConst ``Pure [info.u, info.v]) info.m)
  let cachedPure := mkApp2 (mkConst ``Pure.pure [info.u, info.v]) info.m instPure
  let cachedPure ← instantiateMVars cachedPure -- try to get rid of metavariables eagerly
  set { s with monadInstanceCache := { s.monadInstanceCache with cachedPure := some cachedPure } : State}
  return cachedPure

/-- The expression ``pure (α:=α) e``. -/
def mkPureApp (α e : Expr) : DoElabM Expr := do
  let e ← Term.ensureHasType α e
  return mkApp2 (← getCachedPure) α e

/-- Create a `DoElemCont` returning the result using `pure`. -/
def DoElemCont.mkPure (resultType : Expr) : TermElabM DoElemCont := do
  let r ← mkFreshUserName `r
  return {
    resultName := r,
    resultType,
    k := do
      if (← read).deadCode then
        -- There is no dead syntax here. Just return a fresh metavariable.
        return ← mkFreshExprMVar (← mkMonadicType resultType)
      mkPureApp resultType (← getFVarFromUserName r),
    kind := .duplicable
    ref := .missing
    declKind := .implDetail  -- Does not matter much, because `mkPureApp` does not do
                             -- type class synthesis.
  }

/-- The cached `@Bind.bind m instBind` expression. -/
private def getCachedBind : DoElabM Expr := do
  let s ← get
  if let some cachedBind := s.monadInstanceCache.cachedBind then return cachedBind
  let info := (← read).monadInfo
  let instBind ← Term.mkInstMVar (mkApp (mkConst ``Bind [info.u, info.v]) info.m)
  let cachedBind := mkApp2 (mkConst ``Bind.bind [info.u, info.v]) info.m instBind
  let cachedBind ← instantiateMVars cachedBind -- try to get rid of metavariables eagerly
  set { s with monadInstanceCache := { s.monadInstanceCache with cachedBind := some cachedBind } : State}
  return cachedBind

/-- The expression ``Bind.bind (α:=α) (β:=β) e k``. -/
def mkBindApp (α β e k : Expr) : DoElabM Expr := do
  let mα ← mkMonadicType α
  let e ← Term.ensureHasType mα e
  let k ← Term.ensureHasType (← mkArrow α (← mkMonadicType β)) k
  let cachedBind ← getCachedBind
  return mkApp4 cachedBind α β e k

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
def mkFreshResultType (userName := `α) : DoElabM Expr := do
  mkFreshExprMVar (mkSort (mkLevelSucc (← read).monadInfo.u)) (userName := userName)

def synthUsingDefEq (msg : String) (expected : Expr) (actual : Expr) : DoElabM Unit := do
  unless ← isDefEq expected actual do
    throwError "Failed to synthesize {msg}. {expected} is not definitionally equal to {actual}."

/--
Has the effect of ``e >>= fun (x : eResultTy) => $(← k `(x))``.
-/
def mkBindCancellingPure (x : Name) (eResultTy e : Expr) (k : Expr → DoElabM Expr) (declKind : LocalDeclKind := .default) : DoElabM Expr := do
  -- The .ofBinderName below is mainly to interpret `__do_lift` binders as implementation details.
  let declKind := if declKind matches .default then .ofBinderName x else declKind
  withLocalDecl x .default eResultTy (kind := declKind) fun x => do
    let body ← k x
    let body' := body.consumeMData
    if body.isAppOfArity ``Pure.pure 4 && body'.getArg! 3 == x then
      if ← isDefEq body' (← mkPureApp eResultTy x) then
        return e
    let kResultTy ← mkFreshResultType `kResultTy
    let body ← Term.ensureHasType (← mkMonadicType kResultTy) body
    let k ← mkLambdaFVars #[x] body
    mkBindApp eResultTy kResultTy e k

/--
Like `controlAt TermElabM`, but it maintains the state using the `DoElabM`'s ref cell instead of returning it
in the `TermElabM` result. This makes it possible to run multiple `DoElabM` computations in a row.
-/
def controlAtTermElabM (k : (runInBase : ∀ {β}, DoElabM β → TermElabM β) → TermElabM α) : DoElabM α := fun ctx ref => do
  k (· ctx ref)

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
def addReachingDefsAsNonDep (rootCtx childCtx : LocalContext) (tunneledVars : Std.HashMap Name α) : LocalContext := Id.run do
  let tunnelDecls := childCtx.findFromUserNames tunneledVars (start := rootCtx.numIndices)
  let mut rootCtx := rootCtx
  for decl in tunnelDecls do
    rootCtx := rootCtx.addDecl (decl.setNondep true)
  return rootCtx

/--
Creates a new continuation variable of type `m α` given the result type `α`.
The `tunneledVars` is a superset of the `let`-bound variable names that the jumps will refer to.
Often it will be the `mut` variables. Leaving it empty inlines `let`-bound variables at jump sites.
-/
def mkFreshContVar (resultType : Expr) (tunneledVars : Array Name) : DoElabM ContVarId := do
  let name ← mkFreshId
  let contVarId := ContVarId.mk name
  let type ← mkMonadicType resultType
  let tunneledVars := Std.HashSet.ofArray tunneledVars
  let cvInfo := { type, jumps := #[], lctx := (← getLCtx), tunneledVars }
  modify fun s => { s with contVars := s.contVars.insert contVarId cvInfo }
  return contVarId

def ContVarId.find (contVarId : ContVarId) : DoElabM ContVarInfo := do
  match (← get).contVars.get? contVarId with
  | some info => return info
  | none => throwError "contVarId {contVarId.name} not found"

/-- Creates a new jump site for the continuation variable, to be synthesized later. -/
def ContVarId.mkJump (contVarId : ContVarId) : DoElabM Expr := do
  let info ← contVarId.find
  let lctx := addReachingDefsAsNonDep info.lctx (← getLCtx) info.tunneledVars.inner
  let mvar ← withLCtx' lctx (mkFreshExprMVar info.type) -- assigned by `synthesizeJumps`
  unless (← read).deadCode do -- If it's dead code, don't even bother registering the jump
    let jumps := info.jumps.push { mvar, ref := (← getRef) }
    modify fun s => { s with contVars := s.contVars.insert contVarId { info with jumps } }
  return mvar

/-- The number of jump sites allocated for the continuation variable. -/
def ContVarId.jumpCount (contVarId : ContVarId) : DoElabM Nat := do
  let info ← contVarId.find
  return info.jumps.size

/--
Synthesize the jump sites for the continuation variable.
`k` is run once for each jump site, in the `LocalContext` of the jump site.
The result of `k` is used to fill in the jump site.
-/
def ContVarId.synthesizeJumps (contVarId : ContVarId) (k : DoElabM Expr) : DoElabM Unit := do
  let info ← contVarId.find
  for jump in info.jumps do
    jump.mvar.mvarId!.withContext do withRef jump.ref do
      let res ← k
      synthUsingDefEq "jump site" jump.mvar res

/--
Adds the given local declaration to the local context of the metavariable of each jump site.
This is useful for adding, e.g. join point declarations post-hoc to the local context of the jump
sites.
-/
def ContVarId.addDeclToJumpSites! (contVarId : ContVarId) (decl : LocalDecl) : DoElabM Unit := do
  let info ← contVarId.find
  for jump in info.jumps do
    let mut mvarId := jump.mvar.mvarId!
    repeat
      let found ← mvarId.withContext do return (← getLCtx).find? decl.fvarId |>.isSome
      unless found do
        mvarId.modifyLCtx fun lctx => lctx.addDecl decl
      -- A simple `instantiateMVars` is not enough here because of functions like
      -- `MkBinding.elimApp` which go through one layer of assignment at a time.
      if let some assignment ← getExprMVarAssignment? mvarId then
        mvarId := assignment.getAppFn.mvarId!
      else
        break

def ContVarId.erase (contVarId : ContVarId) : DoElabM Unit := do
  modify fun s => { s with contVars := s.contVars.erase contVarId }

/--
The subset of `(← read).mutVars` that were reassigned at any of the jump sites of the continuation
variable relative to `rootCtx`. The result array has the same order as `(← read).mutVars`.
-/
def ContVarId.getReassignedMutVars (contVarId : ContVarId) (rootCtx : LocalContext) : DoElabM (Std.HashSet Name) := do
  let info ← contVarId.find
  let childCtxs ← info.jumps.mapM fun j => return (← j.mvar.mvarId!.getDecl).lctx
  return Lean.Elab.Do.getReassignedMutVars rootCtx (.ofArray <| (← read).mutVars.map (·.getId)) childCtxs

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
  let newCtx := addReachingDefsAsNonDep oldLCtx (← getLCtx) tunneledDefs
  withLCtx' newCtx <| withReader (fun ctx => { ctx with
    mutVars := oldMutVars,
    mutVarDefs := oldMutVarDefs
  }) k

/--
Return `$e >>= fun ($dec.resultName : $dec.resultType) => $(← dec.k)`, cancelling
the bind if `$(← dec.k)` is `pure $dec.resultName`.
-/
def DoElemCont.mkBindUnlessPure (dec : DoElemCont) (e : Expr) : DoElabM Expr := do
  mkBindCancellingPure dec.resultName dec.resultType e (declKind := dec.declKind) fun _ =>
    withRef? dec.ref dec.k

/--
Return `let $k.resultName : PUnit := PUnit.unit; $(← k.k)`, ensuring that the result type of `k.k`
is `PUnit` and then immediately zeta-reduce the `let`.
-/
def DoElemCont.continueWithUnit (dec : DoElemCont) : DoElabM Expr := do
  let unit ← mkPUnitUnit
  discard <| Term.ensureHasType dec.resultType unit
  mapLetDeclZeta dec.resultName (← mkPUnit) unit (nondep := true) (kind := dec.declKind) fun _ =>
    withRef? dec.ref dec.k

partial def withSynthesizeForDo (k : DoElabM α) : DoElabM α :=
  controlAtTermElabM fun runInBase => do
    let pendingMVarsSaved := (← get).pendingMVars
    modify fun s => { s with pendingMVars := [] }
    try runInBase do
      let a ← k
      synth
      return a
    finally
      modify fun s => { s with pendingMVars := s.pendingMVars ++ pendingMVarsSaved }
where
  isPostponedSyntheticMVarOfMonadicType (mvarId : MVarId) : DoElabM Bool := do
    let some decl ← Term.getSyntheticMVarDecl? mvarId | return false
    let .postponed .. := decl.kind | return false
    let α ← mkFreshResultType
    let mα ← mkMonadicType α
    return ← withNewMCtxDepth (isDefEq (← mvarId.getType) mα) -- Not relevant if

  getSomeSyntheticMVarsRef : DoElabM Syntax := do
    for mvarId in (← liftM (m := TermElabM) get).pendingMVars do
      if let some decl ← Term.getSyntheticMVarDecl? mvarId then
        if decl.stx.getPos?.isSome then
          return decl.stx
    return .missing
  synth : DoElabM Unit := do
    let rec loop (_ : Unit) : DoElabM Unit := do
      withRef (← getSomeSyntheticMVarsRef) <| withIncRecDepth do
        if ← (← liftM (m := TermElabM) get).pendingMVars.anyM isPostponedSyntheticMVarOfMonadicType then
          if ← Term.synthesizeSyntheticMVarsStep (postponeOnError := true) (runTactics := false) then
            loop ()
          Term.tryPostpone
    loop ()

/-- Elaborate the `DoElemCont` with the `deadCode` flag set to `true` to emit warnings. -/
def DoElemCont.elabAsDeadCode (dec : DoElemCont) : DoElabM Unit := do
  withReader (fun ctx => { ctx with deadCode := true }) do
    withLocalDecl dec.resultName .default (← mkFreshResultType) (kind := .implDetail) fun _ => do
      let s ← Term.saveState
      discard <| dec.k
      let msg ← Core.getMessageLog -- case in point! capture it
      s.restore
      Core.setMessageLog msg

/--
Call `caller` with a duplicable proxy of `dec`.
When the proxy is elaborated more than once, a join point is introduced so that `dec` is only
elaborated once to fill in the RHS of this join point.

This is useful for control-flow constructs like `if` and `match`, where multiple tail-called
branches share the continuation.
-/
def DoElemCont.withDuplicableCont (nondupDec : DoElemCont) (caller : DoElemCont → DoElabM Expr) : DoElabM Expr := do
  if nondupDec.kind matches .duplicable .. then
    return (← caller nondupDec)
  let γ := (← read).doBlockResultType
  let mγ ← mkMonadicType γ
  let rootCtx ← getLCtx
  let mutVars := (← read).mutVars
  let mutVarNames := mutVars.map (·.getId)
  let contVarId ← mkFreshContVar γ (mutVarNames.push nondupDec.resultName)
  let duplicableDec := { nondupDec with k := contVarId.mkJump, kind := .duplicable }
  let e ← withSynthesizeForDo (caller duplicableDec)

  -- Now determine whether we need to realize the join point.
  let jumpCount ← contVarId.jumpCount
  if jumpCount = 0 then
    -- Do nothing. No MVar needs to be assigned. However, do elaborate the continuation as dead code
    -- for warnings.
    nondupDec.elabAsDeadCode
    Term.ensureHasType mγ e
  else if jumpCount = 1 then
    -- Linear use of the continuation. Do not introduce a join point; just emit the continuation
    -- directly.
    contVarId.synthesizeJumps nondupDec.k
    let e ← Term.ensureHasType mγ e
    return e
  else -- jumps.size > 1
    -- Non-linear use of the continuation. Introduce a join point and synthesize jumps to it.

    -- Compute the union of all reassigned mut vars. These + `r` constitute the parameters
    -- of the join point. We take a little care to preserve the declaration order that is manifest
    -- in the array `(← read).mutVars`.
    let reassignedMutVars ← contVarId.getReassignedMutVars rootCtx
    let reassignedMutVars := mutVars.filter (reassignedMutVars.contains ·.getId)

    -- Assign the `joinTy` based on the types of the reassigned mut vars and the result type.
    let reassignedDecls ← reassignedMutVars.mapM (getLocalDeclFromUserName ·.getId)
    let reassignedTys := reassignedDecls.map (·.type)
    let joinTy ← mkArrowN (reassignedTys.push nondupDec.resultType) mγ

    -- Assign the `joinRhs` with the result of the continuation.
    let joinRhs ← withLCtx' rootCtx do
      let xs := reassignedDecls.map (fun d => (d.userName, d.type))
        |>.push (nondupDec.resultName, nondupDec.resultType)
      withLocalDeclsDND xs fun xs => do
        for (decl, x) in reassignedDecls.zip xs do
          let id := x.fvarId!
          if let some baseId := (← read).mutVarDefs[decl.userName]? then
            if id != baseId then
              pushInfoLeaf <| .ofFVarAliasInfo { userName := decl.userName, id, baseId }
        mkLambdaFVars xs (← nondupDec.k)

    withLetDecl (← mkFreshUserName `__do_jp) joinTy joinRhs (kind := .implDetail) (nondep := true) fun jp => do
      let decl ← jp.fvarId!.getDecl
      -- Add the join point decl to every jump site metavariable, so that we can assign the jump
      -- sites in the next step.
      contVarId.addDeclToJumpSites! decl
      -- Finally, assign the MVars with the jump to `jp`.
      contVarId.synthesizeJumps do
        let r ← getFVarFromUserName nondupDec.resultName
        let mut jump := jp
        for x in reassignedMutVars do
          let newDefn ← getLocalDeclFromUserName x.getId
          Term.addTermInfo' x newDefn.toExpr
          jump := mkApp jump newDefn.toExpr
        return mkApp jump (← Term.ensureHasType nondupDec.resultType r "Mismatched result type for match arm. It")
      -- Now instantiate the metavariables in `e` to ensure that `abstract` sees all FVar
      -- occurrences of `jp`, rather than trusting, e.g. `Expr.hasFVar` or some cache.
      let e ← instantiateMVars e
      mkLetFVars #[jp] (generalizeNondepLet := false) (← Term.ensureHasType mγ e)

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

def getReturnCont : DoElabM DoElemCont := do
  return (← read).contInfo.toContInfo.returnCont

def getBreakCont : DoElabM (Option (DoElabM Expr)) := do
  return (← read).contInfo.toContInfo.breakCont

def getContinueCont : DoElabM (Option (DoElabM Expr)) := do
  return (← read).contInfo.toContInfo.continueCont

/--
Introduce proxy redefinitions for *all* mut vars and call the continuation `k` with a function
`elimProxyDefs : Expr → MetaM Expr` similar to `mkLetFVars` that will replace the proxy defs with
the actual reassigned or original definitions.
-/
@[inline]
def withProxyMutVarDefs [Inhabited α] (k : (Expr → MetaM Expr) → DoElabM α) : DoElabM α := do
  let mutVars := (← read).mutVars
  let outerCtx ← getLCtx
  let outerDecls := mutVars.map (outerCtx.getFromUserName! ·.getId)
  withLocalDeclsDND (← outerDecls.mapM fun x => do return (x.userName, x.type)) (kind := .implDetail) fun proxyDefs => do
    let proxyCtx ← getLCtx
    let elimProxyDefs e : MetaM Expr := do
      let innerCtx ← getLCtx
      let actualDefs := proxyDefs.map fun pDef =>
        let x := (proxyCtx.getFVar! pDef).userName
        let iDef := (innerCtx.getFromUserName! x).toExpr
        if iDef == pDef then
          (outerCtx.getFromUserName! x).toExpr  -- original definition
        else
          iDef                                  -- reassigned definition
      let e ← elimMVarDeps proxyDefs e
      return e.replaceFVars proxyDefs actualDefs
    k elimProxyDefs

/--
Prepare the context for elaborating the body of a loop.
This includes setting the return continuation, break continuation, continue continuation, as
well as the changed result type of the `do` block in the loop body.
-/
def enterLoopBody (resultType : Expr) (returnCont : DoElemCont) (breakCont continueCont : DoElabM Expr) : (body : DoElabM α) → DoElabM α :=
  let contInfo := ContInfo.toContInfoRef { breakCont, continueCont, returnCont }
  withReader fun ctx => { ctx with contInfo, doBlockResultType := resultType }

/--
Prepare the context for elaborating the body of a `do` block that does not support `mut` vars,
`break`, `continue` or `return`.
-/
def withoutControl (k : DoElabM Expr) : DoElabM Expr := do
  let error := throwError "This `do` block does not support `break`, `continue` or `return`."
  let dec ← getReturnCont
  let contInfo := { breakCont := error, continueCont := error, returnCont := { dec with k := error }}
  let contInfo := ContInfo.toContInfoRef contInfo
  withReader (fun ctx => { ctx with contInfo }) k

/--
Prepare the context for elaborating the body of a `finally` block.
There is no support for `mut` vars, `break`, `continue` or `return` in a `finally` block.
-/
def enterFinally (resultType : Expr) (k : DoElabM Expr) : DoElabM Expr := do
  withoutControl do
  withReader (fun ctx => { ctx with doBlockResultType := resultType }) k

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
  let returnCont ← DoElemCont.mkPure resultType
  let contInfo := ContInfo.toContInfoRef { returnCont }
  return { monadInfo := mi, doBlockResultType := resultType, contInfo }

/--
Inside a dependent `match` arm, the expected type can be refined. This function takes apart the
new expected type and runs the action with an updated `doBlockResultType` accordingly.
-/
def withRefinedExpectedType (ty? : Option Expr) (k : DoElabM α) : DoElabM α := do
  let some ty := ty? | return (← k)
  let (mi, resultType) ← extractMonadInfo ty
  unless ← isDefEq (← read).monadInfo.m mi.m do
    throwError "The expected type {ty} changes the monad from {(← read).monadInfo.m} to {mi.m}. This is not supported by the `do` elaborator."
  -- If we ever support more fine-grained `return`-to-`do`-label, the following will become more complicated.
  let returnCont ← DoElemCont.mkPure resultType
  let contInfo := { (← read).contInfo.toContInfo with returnCont }
  withReader (fun ctx => { ctx with doBlockResultType := resultType, contInfo := contInfo.toContInfoRef }) k
  -- withReader id k

def doElabToSyntax (hint : MessageData) (doElab : DoElabM Expr) (k : Term → DoElabM α) (ref : Syntax := .missing) : DoElabM α :=
  controlAtTermElabM fun runInBase =>
    Term.elabToSyntax (hint? := hint) (ref := ref)
      (runInBase <| withRefinedExpectedType · doElab) (runInBase ∘ k)

/--
  Backtrackable state for the `TermElabM` monad.
-/
structure SavedState where
  «term» : Term.SavedState
  «do» : State
  deriving Nonempty

def SavedState.restore (s : SavedState) : DoElabM Unit := do
  s.term.restore
  set s.do

protected def DoElabM.saveState : DoElabM SavedState :=
  return { «term» := (← Term.saveState), «do» := (← get) }

instance : MonadBacktrack SavedState DoElabM where
  saveState      := DoElabM.saveState
  restoreState b := b.restore

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
    -- letIdLhs := binderIdent >> checkWsBefore "expected space before binders" >> many (ppSpace >> letIdBinder)) >> optType
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
  else if k == ``Parser.Term.let then
    letDeclHasBinders stx[1]
  else if k == ``Parser.Term.doLet then
    letDeclHasBinders stx[2]
  else if k == ``Parser.Term.doLetArrow then
    letDeclArgHasBinders stx[2]
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
        throwErrorAt stx "cannot lift `(<- ...)` over inconsistent syntax variants, consider lifting out the binding manually"
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
        throwErrorAt stx "cannot lift `(<- ...)` over a binder, this error usually happens when you are trying to lift a method nested in a `fun`, `let`, or `match`-alternative, and it can often be fixed by adding a missing `do`"
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

def expandNestedActions (doElem : TSyntax `doElem) : DoElabM (Array (TSyntax `doElem) × TSyntax `doElem) := do
  if !hasNestedActionsToLift doElem.raw then
    return (#[], doElem)
  else
    let baseId ← withFreshMacroScope (MonadQuotation.addMacroScope `__do_lift)
    let (doElem, doElemsNew) ← (expandNestedActionsAux baseId false false doElem).run #[]
    return (doElemsNew, ⟨doElem⟩)

private def withTermInfoContext' (elaborator : Name) (stx : Syntax) (expectedType : Expr) (x : DoElabM Expr) : DoElabM Expr :=
  controlAtTermElabM fun runInBase =>
    Term.withTermInfoContext' elaborator stx (expectedType? := expectedType) (runInBase x)

private def elabDoElemFns (stx : TSyntax `doElem) (cont : DoElemCont)
    (fns : List (KeyedDeclsAttribute.AttributeEntry DoElab)) : DoElabM Expr := do
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
            else if id == postponeExceptionId then
              -- s.restore -- TODO: figure out if this is the right thing to do
              throw ex
            else
              throw ex
          | _ => throw ex

mutual
partial def elabDoElem (stx : TSyntax `doElem) (cont : DoElemCont) : DoElabM Expr := do
  let k := stx.raw.getKind
  trace[Elab.do.step] "do element: {stx}"
  checkSystem "do element elaborator"
  profileitM Exception "do element elaborator" (decl := k) (← getOptions) <|
  withRef stx <| withIncRecDepth <| withFreshMacroScope <| do
  let mγ ← mkMonadicType (← read).doBlockResultType
  if (← read).deadCode then
    logWarningAt stx "This `do` element and its control-flow region are dead code. Consider removing it."
    return ← mkFreshExprMVar mγ
  let env ← getEnv
  let result ← match (← liftMacroM (expandMacroImpl? env stx)) with
  | some (decl, stxNew?) =>
    let stxNew ← liftMacroM <| liftExcept stxNew?
    withTermInfoContext' decl stx mγ <|
      Term.withMacroExpansion stx stxNew <|
        withRef stxNew <| elabDoElem ⟨stxNew⟩ cont
  | none =>
    let (liftedElems, doElem) ← expandNestedActions stx
    if liftedElems.isEmpty then
      match doElemElabAttribute.getEntries (← getEnv) k with
      | []      => throwError "elaboration function for `{k}` has not been implemented{indentD stx}"
      | elabFns => elabDoElemFns stx cont elabFns
    else
      elabDoElems1 (liftedElems.push doElem) cont

partial def elabDoElems1 (doElems : Array (TSyntax `doElem)) (cont : DoElemCont) : DoElabM Expr := do
  if h : doElems.size = 0 then
    throwError "Empty array of `do` elements passed to `elabDoElems1`."
  else
  let back := doElems.back
  let unit ← mkPUnit
  let r ← mkFreshUserName `r
  let mkCont el k := DoElemCont.mk r unit k .nonDuplicable el .implDetail
  doElems.pop.foldr (init := elabDoElem back cont) fun el k => elabDoElem el (mkCont el k)
end

def elabDoSeq (doSeq : TSyntax ``Lean.Parser.Term.doSeq) (cont : DoElemCont) : DoElabM Expr := do
  if (← read).deadCode then
    logWarningAt doSeq "This `do` sequence is dead code. Consider removing it."
    return ← mkFreshExprMVar (← mkMonadicType (← read).doBlockResultType)
  elabDoElems1 (Lean.Parser.Term.getDoElems doSeq) cont

@[builtin_doElem_elab doElemNoNestedAction] def elabDoElemNoNestedAction : DoElab := fun stx cont => do
  let `(doElemNoNestedAction| $e:doElem) := stx | throwUnsupportedSyntax
  elabDoElem e cont

-- @[builtin_term_elab «do»]
def elabDo : Term.TermElab := fun e expectedType? => do
  let `(do $doSeq) := e | throwError "unexpected `do` block syntax{indentD e}"
  Term.tryPostponeIfNoneOrMVar expectedType?
  let ctx ← mkContext expectedType?
  let cont ← DoElemCont.mkPure ctx.doBlockResultType -- same as `($(← returnCont) $resultName)
  let res ← elabDoSeq doSeq cont |>.run ctx |>.run' {}
  Term.synthesizeSyntheticMVars
  let res ← instantiateMVars res
  trace[Elab.do] "{res}"
  pure res

syntax:arg (name := dooBlock) "doo" doSeq : term

@[builtin_term_elab «dooBlock»]
def elabDooBlock : Term.TermElab := fun e expectedType? => do
  let `(doo $doSeq) := e | throwError "unexpected `do` block syntax{indentD e}"
  elabDo (← `(do $doSeq)) expectedType?

def elabNestedAction (stx : Syntax) (_expectedType? : Option Expr) : TermElabM Expr := do
  let `(← $_rhs) := stx | throwUnsupportedSyntax
  throwError "Nested action `{stx}` must be nested inside a `do` expression."
