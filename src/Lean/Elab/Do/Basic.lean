/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Binders
import Lean.Meta.ProdN
import Init.Omega

public section

namespace Lean.Elab.Do

open Lean Meta

builtin_initialize registerTraceClass `Elab.do

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
  mutVars : Array Name := #[]
  /--
  The expected type of the current `do` block.
  This can be different from `earlyReturnType` in `for` loop `do` blocks, for example.
  -/
  doBlockResultType : Expr
  /-- Information about `return`, `break` and `continue` continuations. -/
  contInfo : ContInfoRef

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
  /-- The name of the monadic result variable. -/
  resultName : Name
  /-- The type of the monadic result. -/
  resultType : Expr
  /-- The continuation to elaborate the `rest` of the block. -/
  k : DoElabM Expr
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
  set { s with monadInstanceCache := { s.monadInstanceCache with cachedPure := some cachedPure } : State}
  return cachedPure

/-- The expression ``pure (α:=α) e``. -/
def mkPureApp (α e : Expr) : DoElabM Expr := do
  let e ← Term.ensureHasType α e
  return mkApp2 (← getCachedPure) α e

/-- Create a `DoElemCont` returning the result using `pure`. -/
def DoElemCont.mkPure (resultType : Expr) : TermElabM DoElemCont := do
  let r ← mkFreshUserName `r
  return { resultName := r, resultType, k := do mkPureApp resultType (← getFVarFromUserName r) }

/-- The cached `@Bind.bind m instBind` expression. -/
private def getCachedBind : DoElabM Expr := do
  let s ← get
  if let some cachedBind := s.monadInstanceCache.cachedBind then return cachedBind
  let info := (← read).monadInfo
  let instBind ← Term.mkInstMVar (mkApp (mkConst ``Bind [info.u, info.v]) info.m)
  let cachedBind := mkApp2 (mkConst ``Bind.bind [info.u, info.v]) info.m instBind
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
def declareMutVar (x : Name) : DoElabM α → DoElabM α :=
  withReader fun ctx => { ctx with mutVars := ctx.mutVars.push x }

/-- Register the given name as that of a `mut` variable if the syntax token `mut` is present. -/
def declareMutVar? (mutTk? : Option Syntax) (x : Name) (k : DoElabM α) : DoElabM α :=
  if mutTk?.isSome then declareMutVar x k else k

/-- Throw an error if the given name is not a declared `mut` variable. -/
def throwUnlessMutVarDeclared (x : Name) : DoElabM Unit := do
  unless (← read).mutVars.contains x do
    throwError "undeclared mutable variable `{x}`"

/-- Throw an error if a declaration of the given name would shadow a `mut` variable. -/
def checkMutVarsForShadowing (x : Name) : DoElabM Unit := do
  if (← read).mutVars.contains x then
    throwError "mutable variable `{x.simpMacroScopes}` cannot be shadowed"

/-- Create a fresh `α` that would fit in `m α`. -/
def mkFreshResultType (userName := `α) : DoElabM Expr := do
  mkFreshExprMVar (mkSort (mkLevelSucc (← read).monadInfo.u)) (userName := userName)

def synthUsingDefEq (msg : String) (expected : Expr) (actual : Expr) : DoElabM Unit := do
  unless ← isDefEq expected actual do
    throwError "Failed to synthesize {msg}. {expected} is not definitionally equal to {actual}."

/--
Has the effect of ``e >>= fun (x : eResultTy) => $(← k `(x))``.
Ensures that `e` has type `m eResultTy`.
-/
def mkBindCancellingPure (x : Name) (eResultTy e : Expr) (k : Expr → DoElabM Expr) : DoElabM Expr := do
  withLocalDeclD x eResultTy fun x => do
    let body ← k x
    let body' := body.consumeMData
    if body'.isAppOfArity ``Pure.pure 4 && body'.getArg! 3 == x then
      return e
    let kResultTy ← mkFreshResultType `kResultTy
    let k ← mkLambdaFVars #[x] body
    mkBindApp eResultTy kResultTy e k

/--
A variant of `Term.elabType` that takes the universe of the monad into account, unless
`freshLevel` is set.
-/
def elabType (ty? : Option (TSyntax `term)) (freshLevel := false) : DoElabM Expr := do
  let u ← if freshLevel then mkFreshLevelMVar else (mkLevelSucc ·.monadInfo.u) <$> read
  let sort := mkSort u
  match ty? with
  | none => mkFreshExprMVar sort
  | some ty => Term.elabTermEnsuringType ty sort

private partial def withPendingMVars (k : TermElabM α) : TermElabM (α × List MVarId) := do
  let pendingMVarsSaved := (← get).pendingMVars
  modify fun s => { s with pendingMVars := [] }
  try
    let a ← k
    let pendingMVars := (← get).pendingMVars
    return (a, pendingMVars)
  finally
    modify fun s => { s with pendingMVars := s.pendingMVars ++ pendingMVarsSaved }

def elabTerm (stx : Syntax) (expectedType? : Option Expr) : DoElabM Expr := do
  let (e, _pendingMVars) ← withPendingMVars <| Term.elabTerm stx expectedType?
  -- for mvarId in pendingMVars.reverse do
  --   let some mvarDecl ← Term.getSyntheticMVarDecl? mvarId | continue
  --   let .postponed _ := mvarDecl.kind | continue
  --   match mvarDecl.stx with
  --   | `(<== $e) => logInfo m!"Elaborate {e}"
  --   | _ => continue
  return e

def elabTermEnsuringType (stx : Syntax) (expectedType? : Option Expr) : DoElabM Expr := do
  let e ← Term.elabTermEnsuringType stx expectedType?
  -- nandle nested actions
  return e

def elabBinder (binder : Syntax) (x : Expr → DoElabM α) : DoElabM α := do
  controlAt TermElabM fun runInBase => Term.elabBinder binder (runInBase ∘ x)

/--
The subset of `mutVars` that were reassigned in any of the `childCtxs` relative to the given
`rootCtx`.
-/
def getReassignedMutVars (rootCtx : LocalContext) (mutVars : Std.HashSet Name) (childCtxs : Array LocalContext) : Std.HashSet Name := Id.run do
  let mut reassignedMutVars := Std.HashSet.emptyWithCapacity mutVars.size
  for childCtx in childCtxs do
    let newDefs := childCtx.findFromUserNames mutVars (start := rootCtx.numIndices)
    reassignedMutVars := reassignedMutVars.insertMany (newDefs.map (·.userName))
  return reassignedMutVars

/--
Adds the new reaching definitions of the given `tunneledVars` in `childCtx` relative to `rootCtx` as
non-dependent decls.
-/
def addReachingDefsAsNonDep (rootCtx childCtx : LocalContext) (tunneledVars : Std.HashSet Name) : LocalContext := Id.run do
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
  let lctx := addReachingDefsAsNonDep info.lctx (← getLCtx) info.tunneledVars
  let mvar ← withLCtx' lctx (mkFreshExprMVar info.type)
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
      fullApproxDefEq <| synthUsingDefEq "jump site" jump.mvar res

def ContVarId.erase (contVarId : ContVarId) : DoElabM Unit := do
  modify fun s => { s with contVars := s.contVars.erase contVarId }

/--
The subset of `(← read).mutVars` that were reassigned at any of the jump sites of the continuation
variable. The result array has the same order as `(← read).mutVars`.
-/
def ContVarId.getReassignedMutVars (contVarId : ContVarId) (rootCtx : LocalContext) : DoElabM (Std.HashSet Name) := do
  let info ← contVarId.find
  let childCtxs ← info.jumps.mapM fun j => return (← j.mvar.mvarId!.getDecl).lctx
  return Lean.Elab.Do.getReassignedMutVars rootCtx (.ofArray (← read).mutVars) childCtxs

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
def withLCtxKeepingMutVarDefs (oldCtx : LocalContext) (oldMutVars : Array Name) (resultName : Name) (k : DoElabM α) : DoElabM α := do
  let newCtx := addReachingDefsAsNonDep oldCtx (← getLCtx) (.ofArray <| oldMutVars.push resultName)
  withLCtx' newCtx <| withReader (fun ctx => { ctx with mutVars := oldMutVars }) k

/--
Return `$e >>= fun ($dec.resultName : $dec.resultType) => $(← dec.k)`, cancelling
the bind if `$(← dec.k)` is `pure $dec.resultName`.
-/
def DoElemCont.mkBindUnlessPure (dec : DoElemCont) (e : Expr) : DoElabM Expr := do
  mkBindCancellingPure dec.resultName dec.resultType e (fun _ => dec.k)

/--
Return `let $k.resultName : PUnit := PUnit.unit; $(← k.k)`, ensuring that the result type of `k.k`
is `PUnit` and then immediately zeta-reduce the `let`.
-/
def DoElemCont.continueWithUnit (dec : DoElemCont) : DoElabM Expr := do
  let unit ← mkPUnitUnit
  discard <| Term.ensureHasType dec.resultType unit
  mapLetDeclZeta dec.resultName (← mkPUnit) unit (fun _ => dec.k)

/--
Call `caller` with a duplicable proxy of `dec`.
When the proxy is elaborated more than once, a join point is introduced so that `dec` is only
elaborated once to fill in the RHS of this join point.

This is useful for control-flow constructs like `if` and `match`, where multiple tail-called
branches share the continuation.
-/
def DoElemCont.withDuplicableCont (nondupDec : DoElemCont) (caller : DoElemCont → DoElabM Expr) : DoElabM Expr := do
  let α := (← read).doBlockResultType
  let mα ← mkMonadicType α
  let joinTy ← mkFreshExprMVar (mkSort (mkLevelSucc (← read).monadInfo.v)) (userName := `joinTy)
  let joinRhs ← mkFreshExprMVar joinTy (userName := `joinRhs)
  withLetDecl (← mkFreshUserName `__do_jp) joinTy joinRhs (kind := .implDetail) (nondep := true) fun jp => do
    let mutVars := (← read).mutVars
    let contVarId ← mkFreshContVar α (mutVars.push nondupDec.resultName)
    let duplicableDec := { nondupDec with k := contVarId.mkJump }
    let e ← caller duplicableDec

    -- Now determine whether we need to realize the join point.
    let jumpCount ← contVarId.jumpCount
    if jumpCount = 0 then
      -- Do nothing. No MVar needs to be assigned.
      Term.ensureHasType mα e
    else if jumpCount = 1 then
      -- Linear use of the continuation. Do not introduce a join point; just emit the continuation
      -- directly.
      contVarId.synthesizeJumps nondupDec.k
      let e ← Term.ensureHasType mα e
      -- Now zeta-reduce `jp`. Should be a semantic no-op.
      let e ← elimMVarDeps #[jp] e
      return e.replaceFVar jp joinRhs
    else -- jumps.size > 1
      -- Non-linear use of the continuation. Introduce a join point and synthesize jumps to it.

      -- Compute the union of all reassigned mut vars. These + `r` constitute the parameters
      -- of the join point. We take a little care to preserve the declaration order that is manifest
      -- in the array `(← read).mutVars`.
      let reassignedMutVars ← contVarId.getReassignedMutVars (← joinRhs.mvarId!.getDecl).lctx
      let reassignedMutVars := mutVars.filter reassignedMutVars.contains

      -- Assign the `joinTy` based on the types of the reassigned mut vars and the result type.
      let reassignedDecls ← reassignedMutVars.mapM (getLocalDeclFromUserName ·)
      let reassignedTys := reassignedDecls.map (·.type)
      let resTy ← mkFreshResultType
      let joinTy' ← mkArrowN (reassignedTys.push resTy) mα
      synthUsingDefEq "join point type" joinTy joinTy'

      -- Assign the `joinRhs` with the result of the continuation.
      let rhs ← joinRhs.mvarId!.withContext do
        withLocalDeclsDND (reassignedDecls.map (fun d => (d.userName, d.type)) |>.push (nondupDec.resultName, resTy)) fun xs => do
          mkLambdaFVars xs (← nondupDec.k)
      synthUsingDefEq "join point RHS" joinRhs rhs

      -- Finally, assign the MVars with the jump to `jp`.
      contVarId.synthesizeJumps do
        let r ← getFVarFromUserName nondupDec.resultName
        let mut jump := jp
        for name in reassignedMutVars do
          let newDefn ← getLocalDeclFromUserName name
          jump := mkApp jump newDefn.toExpr
        return mkApp jump (← Term.ensureHasType resTy r "Mismatched result type for match arm. It")

      mkLetFVars #[jp] (generalizeNondepLet := false) (← Term.ensureHasType mα e)

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
  let outerDecls := mutVars.map outerCtx.getFromUserName!
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
    let .succ u ← getLevel resultType | return none
    let .succ v ← getLevel type | return none
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

private def elabDoElemFns (stx : TSyntax `doElem) (cont : DoElemCont)
    (fns : List (KeyedDeclsAttribute.AttributeEntry DoElab)) : DoElabM Expr := do
  let s ← saveState
  match fns with
  | [] => throwError "unexpected `do` element syntax{indentD stx}"
  | elabFn :: elabFns =>
    try
      elabFn.value stx cont
    catch ex => match ex with
      | .internal id _ =>
        if id == unsupportedSyntaxExceptionId then
          s.restore
          elabDoElemFns stx cont elabFns
        else
          throw ex
      | _ => throw ex

partial def elabDoElem (stx : TSyntax `doElem) (cont : DoElemCont) : DoElabM Expr := do
  -- withTraceNode `Elab.step (fun _ => return m!"expected type: {expectedType?}, term\n{stx}")
  --   (tag := stx.getKind.toString) do
  let k := stx.raw.getKind
  checkSystem "do element elaborator"
  profileitM Exception "do element elaborator" (decl := k) (← getOptions) <|
  withRef stx <| withIncRecDepth <| withFreshMacroScope <| do
  let env ← getEnv
  let result ← match (← liftMacroM (expandMacroImpl? env stx)) with
  | some (_decl, stxNew?) =>
    let stxNew ← liftMacroM <| liftExcept stxNew?
    -- withTermInfoContext' decl stx (expectedType? := expectedType?) <|
    Term.withMacroExpansion stx stxNew <|
      withRef stxNew <| elabDoElem stx cont
  | none =>
    match doElemElabAttribute.getEntries (← getEnv) k with
    | []      => throwError "elaboration function for `{k}` has not been implemented{indentD stx}"
    | elabFns => elabDoElemFns stx cont elabFns

def elabDoElems1 (doElems : Array (TSyntax `doElem)) (cont : DoElemCont) : DoElabM Expr := do
  if h : doElems.size = 0 then
    throwError "Empty array of `do` elements passed to `elabDoElems1`."
  else
  let back := doElems.back
  let unit ← mkPUnit
  let r ← mkFreshUserName `r
  doElems.pop.foldr (init := elabDoElem back cont) fun el k => elabDoElem el (.mk r unit k)

def elabDoSeq (doSeq : TSyntax ``Lean.Parser.Term.doSeq) (cont : DoElemCont) : DoElabM Expr :=
  elabDoElems1 (Lean.Parser.Term.getDoElems doSeq) cont

syntax:arg (name := dooBlock) "doo" doSeq : term

@[builtin_term_elab «dooBlock»] def elabDooBlock : Term.TermElab := fun e expectedType? => do
  let `(doo $doSeq) := e | throwError "unexpected `do` block syntax{indentD e}"
  Term.tryPostponeIfNoneOrMVar expectedType?
  let ctx ← mkContext expectedType?
  let cont ← DoElemCont.mkPure ctx.doBlockResultType
  let res ← elabDoSeq doSeq cont |>.run ctx |>.run' {}
  trace[Elab.do] "{res}"
  pure res

-- @[builtin_term_elab «do»]
def elabDo : Term.TermElab := fun e expectedType? => do
  let `(do $doSeq) := e | throwError "unexpected `do` block syntax{indentD e}"
  Term.tryPostponeIfNoneOrMVar expectedType?
  let ctx ← mkContext expectedType?
  let cont ← DoElemCont.mkPure ctx.doBlockResultType
  let res ← elabDoSeq doSeq cont |>.run ctx |>.run' {}
  trace[Elab.do] "{res}"
  pure res
