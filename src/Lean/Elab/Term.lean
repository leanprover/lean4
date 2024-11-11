/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.ReservedNameAction
import Lean.Meta.AppBuilder
import Lean.Meta.CollectMVars
import Lean.Meta.Coe
import Lean.Util.CollectLevelMVars
import Lean.Linter.Deprecated
import Lean.Elab.Config
import Lean.Elab.Level
import Lean.Elab.DeclModifiers
import Lean.Elab.PreDefinition.TerminationHint
import Lean.Language.Basic

namespace Lean.Elab

namespace Term

/-- Saved context for postponed terms and tactics to be executed. -/
structure SavedContext where
  declName?  : Option Name
  options    : Options
  openDecls  : List OpenDecl
  macroStack : MacroStack
  errToSorry : Bool
  levelNames : List Name

/-- The kind of a tactic metavariable, used for additional error reporting. -/
inductive TacticMVarKind
  /-- Standard tactic metavariable, arising from `by ...` syntax. -/
  | term
  /-- Tactic metavariable arising from an autoparam for a function application. -/
  | autoParam (argName : Name)
  /-- Tactic metavariable arising from an autoparam for a structure field. -/
  | fieldAutoParam (fieldName structName : Name)

/-- We use synthetic metavariables as placeholders for pending elaboration steps. -/
inductive SyntheticMVarKind where
  /--
  Use typeclass resolution to synthesize value for metavariable.
  If `extraErrorMsg?` is `some msg`, `msg` contains additional information to include in error messages
  regarding type class synthesis failure.
  -/
  | typeClass (extraErrorMsg? : Option MessageData)
  /--
  Use coercion to synthesize value for the metavariable.
  If synthesis fails, then throws an error.
  - If `mkErrorMsg?` is provided, then the error `mkErrorMsg expectedType e` is thrown.
    The `mkErrorMsg` function is allowed to throw an error itself.
  - Otherwise, throws a default type mismatch error message.
    If `header?` is not provided, the default header is "type mismatch".
    If `f?` is provided, then throws an application type mismatch error.
  -/
  | coe (header? : Option String) (expectedType : Expr) (e : Expr) (f? : Option Expr)
      (mkErrorMsg? : Option (MVarId → Expr → Expr → MetaM MessageData))
  /-- Use tactic to synthesize value for metavariable. -/
  | tactic (tacticCode : Syntax) (ctx : SavedContext) (kind : TacticMVarKind)
  /-- Metavariable represents a hole whose elaboration has been postponed. -/
  | postponed (ctx : SavedContext)
  deriving Inhabited

/--
Convert an "extra" optional error message into a message `"\n{msg}"` (if `some msg`) and `MessageData.nil` (if `none`)
-/
def extraMsgToMsg (extraErrorMsg? : Option MessageData) : MessageData :=
  if let some msg := extraErrorMsg? then m!"\n{msg}" else .nil

instance : ToString SyntheticMVarKind where
  toString
    | .typeClass .. => "typeclass"
    | .coe ..       => "coe"
    | .tactic ..    => "tactic"
    | .postponed .. => "postponed"

structure SyntheticMVarDecl where
  stx : Syntax
  kind : SyntheticMVarKind
  deriving Inhabited

/--
  We can optionally associate an error context with a metavariable (see `MVarErrorInfo`).
  We have three different kinds of error context.
-/
inductive MVarErrorKind where
  /-- Metavariable for implicit arguments. `ctx` is the parent application,
  `lctx` is a local context where it is valid (necessary for eta feature for named arguments). -/
  | implicitArg (lctx : LocalContext) (ctx : Expr)
  /-- Metavariable for explicit holes provided by the user (e.g., `_` and `?m`) -/
  | hole
  /-- "Custom", `msgData` stores the additional error messages. -/
  | custom (msgData : MessageData)
  deriving Inhabited

instance : ToString MVarErrorKind where
  toString
    | .implicitArg _ _ => "implicitArg"
    | .hole            => "hole"
    | .custom _        => "custom"

/--
  We can optionally associate an error context with metavariables.
-/
structure MVarErrorInfo where
  mvarId    : MVarId
  ref       : Syntax
  kind      : MVarErrorKind
  deriving Inhabited

/--
When reporting unexpected universe level metavariables, it is useful to localize the errors
to particular terms, especially at `let` bindings and function binders,
where universe polymorphism is not permitted.
-/
structure LevelMVarErrorInfo where
  lctx      : LocalContext
  expr      : Expr
  ref       : Syntax
  msgData?  : Option MessageData := none
  deriving Inhabited

/--
  Nested `let rec` expressions are eagerly lifted by the elaborator.
  We store the information necessary for performing the lifting here.
-/
structure LetRecToLift where
  ref            : Syntax
  fvarId         : FVarId
  attrs          : Array Attribute
  shortDeclName  : Name
  declName       : Name
  lctx           : LocalContext
  localInstances : LocalInstances
  type           : Expr
  val            : Expr
  mvarId         : MVarId
  termination    : TerminationHints
  deriving Inhabited

/--
  State of the `TermElabM` monad.
-/
structure State where
  levelNames        : List Name       := []
  syntheticMVars    : MVarIdMap SyntheticMVarDecl := {}
  pendingMVars      : List MVarId := {}
  /-- List of errors associated to a metavariable that are shown to the user if the metavariable could not be fully instantiated -/
  mvarErrorInfos    : List MVarErrorInfo := []
  /-- List of data to be able to localize universe level metavariable errors to particular expressions. -/
  levelMVarErrorInfos   : List LevelMVarErrorInfo := []
  /--
    `mvarArgNames` stores the argument names associated to metavariables.
    These are used in combination with `mvarErrorInfos` for throwing errors about metavariables that could not be fully instantiated.
    For example when elaborating `List _`, the argument name of the placeholder will be `α`.

    While elaborating an application, `mvarArgNames` is set for each metavariable argument, using the available argument name.
    This may happen before or after the `mvarErrorInfos` is set for the same metavariable.

    We used to store the argument names in `mvarErrorInfos`, updating the `MVarErrorInfos` to add the argument name when it is available,
    but this doesn't work if the argument name is available _before_ the `mvarErrorInfos` is set for that metavariable.
  -/
  mvarArgNames      : MVarIdMap Name := {}
  letRecsToLift     : List LetRecToLift := []
  deriving Inhabited

/--
  Backtrackable state for the `TermElabM` monad.
-/
structure SavedState where
  meta   : Meta.SavedState
  «elab» : State
  deriving Nonempty

end Term

namespace Tactic

/--
  State of the `TacticM` monad.
-/
structure State where
  goals : List MVarId
  deriving Inhabited

/--
  Snapshots are used to implement the `save` tactic.
  This tactic caches the state of the system, and allows us to "replay"
  expensive proofs efficiently. This is only relevant implementing the
  LSP server.
-/
structure Snapshot where
  core   : Core.State
  meta   : Meta.State
  term   : Term.State
  tactic : Tactic.State
  stx    : Syntax

/--
  Key for the cache used to implement the `save` tactic.
-/
structure CacheKey where
  mvarId : MVarId -- TODO: should include all goals
  pos    : String.Pos
  deriving BEq, Hashable, Inhabited

/--
  Cache for the `save` tactic.
-/
structure Cache where
   pre  : PHashMap CacheKey Snapshot := {}
   post : PHashMap CacheKey Snapshot := {}
   deriving Inhabited

section Snapshot
open Language

structure SavedState where
  term   : Term.SavedState
  tactic : State

/-- Snapshot after finishing execution of a tactic. -/
structure TacticFinishedSnapshot extends Language.Snapshot where
  /-- State saved for reuse, if no fatal exception occurred. -/
  state? : Option SavedState
deriving Inhabited
instance : ToSnapshotTree TacticFinishedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, #[]⟩

/-- Snapshot just before execution of a tactic. -/
structure TacticParsedSnapshotData (TacticParsedSnapshot : Type) extends Language.Snapshot where
  /-- Syntax tree of the tactic, stored and compared for incremental reuse. -/
  stx      : Syntax
  /-- Task for nested incrementality, if enabled for tactic. -/
  inner?   : Option (SnapshotTask TacticParsedSnapshot) := none
  /-- Task for state after tactic execution. -/
  finished : SnapshotTask TacticFinishedSnapshot
  /-- Tasks for subsequent, potentially parallel, tactic steps. -/
  next     : Array (SnapshotTask TacticParsedSnapshot) := #[]
deriving Inhabited

/-- State after execution of a single synchronous tactic step. -/
inductive TacticParsedSnapshot where
  | mk (data : TacticParsedSnapshotData TacticParsedSnapshot)
deriving Inhabited
abbrev TacticParsedSnapshot.data : TacticParsedSnapshot → TacticParsedSnapshotData TacticParsedSnapshot
  | .mk data => data
partial instance : ToSnapshotTree TacticParsedSnapshot where
  toSnapshotTree := go where
    go := fun ⟨s⟩ => ⟨s.toSnapshot,
      s.inner?.toArray.map (·.map (sync := true) go) ++
      #[s.finished.map (sync := true) toSnapshotTree] ++
      s.next.map (·.map (sync := true) go)⟩

end Snapshot
end Tactic

namespace Term

structure Context where
  declName? : Option Name := none
  /--
    Map `.auxDecl` local declarations used to encode recursive declarations to their full-names.
  -/
  auxDeclToFullName : FVarIdMap Name  := {}
  macroStack        : MacroStack      := []
  /--
     When `mayPostpone == true`, an elaboration function may interrupt its execution by throwing `Exception.postpone`.
     The function `elabTerm` catches this exception and creates fresh synthetic metavariable `?m`, stores `?m` in
     the list of pending synthetic metavariables, and returns `?m`. -/
  mayPostpone : Bool := true
  /--
     When `errToSorry` is set to true, the method `elabTerm` catches
     exceptions and converts them into synthetic `sorry`s.
     The implementation of choice nodes and overloaded symbols rely on the fact
     that when `errToSorry` is set to false for an elaboration function `F`, then
     `errToSorry` remains `false` for all elaboration functions invoked by `F`.
     That is, it is safe to transition `errToSorry` from `true` to `false`, but
     we must not set `errToSorry` to `true` when it is currently set to `false`. -/
  errToSorry : Bool := true
  /--
     When `autoBoundImplicit` is set to true, instead of producing
     an "unknown identifier" error for unbound variables, we generate an
     internal exception. This exception is caught at `elabBinders` and
     `elabTypeWithUnboldImplicit`. Both methods add implicit declarations
     for the unbound variable and try again. -/
  autoBoundImplicit  : Bool            := false
  autoBoundImplicits : PArray Expr := {}
  /--
    A name `n` is only eligible to be an auto implicit name if `autoBoundImplicitForbidden n = false`.
    We use this predicate to disallow `f` to be considered an auto implicit name in a definition such
    as
    ```
    def f : f → Bool := fun _ => true
    ```
  -/
  autoBoundImplicitForbidden : Name → Bool := fun _ => false
  /-- Map from user name to internal unique name -/
  sectionVars        : NameMap Name    := {}
  /-- Map from internal name to fvar -/
  sectionFVars       : NameMap Expr    := {}
  /-- Enable/disable implicit lambdas feature. -/
  implicitLambda     : Bool            := true
  /-- Heed `elab_as_elim` attribute. -/
  heedElabAsElim     : Bool            := true
  /-- Noncomputable sections automatically add the `noncomputable` modifier to any declaration we cannot generate code for. -/
  isNoncomputableSection : Bool        := false
  /-- When `true` we skip TC failures. We use this option when processing patterns. -/
  ignoreTCFailures : Bool := false
  /-- `true` when elaborating patterns. It affects how we elaborate named holes. -/
  inPattern        : Bool := false
  /-- Cache for the `save` tactic. It is only `some` in the LSP server. -/
  tacticCache?     : Option (IO.Ref Tactic.Cache) := none
  /--
  Snapshot for incremental processing of current tactic, if any.

  Invariant: if the bundle's `old?` is set, then the state *up to the start* of the tactic is
  unchanged, i.e. reuse is possible.
  -/
  tacSnap?         : Option (Language.SnapshotBundle Tactic.TacticParsedSnapshot) := none
  /--
  If `true`, we store in the `Expr` the `Syntax` for recursive applications (i.e., applications
  of free variables tagged with `isAuxDecl`). We store the `Syntax` using `mkRecAppWithSyntax`.
  We use the `Syntax` object to produce better error messages at `Structural.lean` and `WF.lean`. -/
  saveRecAppSyntax : Bool := true
  /--
  If `holesAsSyntheticOpaque` is `true`, then we mark metavariables associated
  with `_`s as `syntheticOpaque` if they do not occur in patterns.
  This option is useful when elaborating terms in tactics such as `refine'` where
  we want holes there to become new goals. See issue #1681, we have
  `refine' (fun x => _)
  -/
  holesAsSyntheticOpaque : Bool := false

abbrev TermElabM := ReaderT Context $ StateRefT State MetaM
abbrev TermElab  := Syntax → Option Expr → TermElabM Expr

/-
Make the compiler generate specialized `pure`/`bind` so we do not have to optimize through the
whole monad stack at every use site. May eventually be covered by `deriving`.
-/
@[always_inline]
instance : Monad TermElabM :=
  let i := inferInstanceAs (Monad TermElabM)
  { pure := i.pure, bind := i.bind }

open Meta

instance : Inhabited (TermElabM α) where
  default := throw default

protected def saveState : TermElabM SavedState :=
  return { meta := (← Meta.saveState), «elab» := (← get) }

def SavedState.restore (s : SavedState) (restoreInfo : Bool := false) : TermElabM Unit := do
  let traceState ← getTraceState -- We never backtrack trace message
  let infoState ← getInfoState -- We also do not backtrack the info nodes when `restoreInfo == false`
  s.meta.restore
  set s.elab
  setTraceState traceState
  unless restoreInfo do
    setInfoState infoState

/--
Like `Meta.withRestoreOrSaveFull` for `TermElabM`, but also takes a `tacSnap?` that
* when running `act`, is set as `Context.tacSnap?`
* otherwise (i.e. on restore) is used to update the new snapshot promise to the old task's
  value.
This extra restore step is necessary because while `reusableResult?` can be used to replay any
effects on `State`, `Context.tacSnap?` is not part of it but changed via an `IO` side effect, so
it needs to be replayed separately.

We use an explicit parameter instead of accessing `Context.tacSnap?` directly because this prevents
`withRestoreOrSaveFull` and `withReader` from being used in the wrong order.
-/
@[specialize]
def withRestoreOrSaveFull (reusableResult? : Option (α × SavedState))
    (tacSnap? : Option (Language.SnapshotBundle Tactic.TacticParsedSnapshot)) (act : TermElabM α) :
    TermElabM (α × SavedState) := do
  if let some (_, state) := reusableResult? then
    set state.elab
    if let some snap := tacSnap? then
      let some old := snap.old?
        | throwError "withRestoreOrSaveFull: expected old snapshot in `tacSnap?`"
      snap.new.resolve old.val.get

  let reusableResult? := reusableResult?.map (fun (val, state) => (val, state.meta))
  let (a, meta) ← withReader ({ · with tacSnap? }) do
    controlAt MetaM fun runInBase => do
      Meta.withRestoreOrSaveFull reusableResult? <| runInBase act
  return (a, { meta, «elab» := (← get) })

instance : MonadBacktrack SavedState TermElabM where
  saveState      := Term.saveState
  restoreState b := b.restore

/--
Incremental elaboration helper. Avoids leakage of data from outside syntax via the monadic context
when running `act` on `stx` by
* setting `stx` as the `ref` and
* deactivating `suppressElabErrors` if `stx` is `missing`-free, which also helps with not hiding
  useful errors in this part of the input. Note that if `stx` has `missing`, this should always be
  true for the outer syntax as well, so taking the old value of `suppressElabErrors` into account
  should not introduce data leakage.

This combinator should always be used when narrowing reuse to a syntax subtree, usually (in the case
of tactics, to be generalized) via `withNarrowed(Arg)TacticReuse`.
-/
def withReuseContext [Monad m] [MonadWithReaderOf Core.Context m] (stx : Syntax) (act : m α) :
    m α := do
  withTheReader Core.Context (fun ctx => { ctx with
      ref := stx
      suppressElabErrors := ctx.suppressElabErrors && stx.hasMissing }) act

/--
Manages reuse information for nested tactics by `split`ting given syntax into an outer and inner
part. `act` is then run on the inner part but with reuse information adjusted as following:
* If the old (from `tacSnap?`'s `SyntaxGuarded.stx`) and new (from `stx`) outer syntax are not
  identical according to `Syntax.eqWithInfo`, reuse is disabled.
* Otherwise, the old syntax as stored in `tacSnap?` is updated to the old *inner* syntax.
* In any case, `withReuseContext` is used on the new inner syntax to further prepare the monadic
  context.

For any tactic that participates in reuse, `withNarrowedTacticReuse` should be applied to the
tactic's syntax and `act` should be used to do recursive tactic evaluation of nested parts.
-/
def withNarrowedTacticReuse [Monad m] [MonadWithReaderOf Core.Context m]
    [MonadWithReaderOf Context m] [MonadOptions m] (split : Syntax → Syntax × Syntax)
    (act : Syntax → m α) (stx : Syntax) : m α := do
  let (outer, inner) := split stx
  let opts ← getOptions
  withTheReader Term.Context (fun ctx => { ctx with tacSnap? := ctx.tacSnap?.map fun tacSnap =>
    { tacSnap with old? := tacSnap.old?.bind fun old => do
      let (oldOuter, oldInner) := split old.stx
      guard <| outer.eqWithInfoAndTraceReuse opts oldOuter
      return { old with stx := oldInner }
    }
  }) do
    withReuseContext inner (act inner)

/--
A variant of `withNarrowedTacticReuse` that uses `stx[argIdx]` as the inner syntax and all `stx`
child nodes before that as the outer syntax, i.e. reuse is disabled if there was any change before
`argIdx`.

NOTE: child nodes after `argIdx` are not tested (which would almost always disable reuse as they are
necessarily shifted by changes at `argIdx`) so it must be ensured that the result of `arg` does not
depend on them (i.e. they should not be inspected beforehand).
-/
def withNarrowedArgTacticReuse [Monad m] [MonadWithReaderOf Core.Context m] [MonadWithReaderOf Context m]
    [MonadOptions m] (argIdx : Nat) (act : Syntax → m α) (stx : Syntax) : m α :=
  withNarrowedTacticReuse (fun stx => (mkNullNode stx.getArgs[:argIdx], stx[argIdx])) act stx

/--
Disables incremental tactic reuse *and* reporting for `act` if `cond` is true by setting `tacSnap?`
to `none`. This should be done for tactic blocks that are run multiple times as otherwise the
reported progress will jump back and forth (and partial reuse for these kinds of tact blocks is
similarly questionable).
-/
def withoutTacticIncrementality [Monad m] [MonadWithReaderOf Context m] [MonadOptions m]
    (cond : Bool) (act : m α) : m α := do
  let opts ← getOptions
  withTheReader Term.Context (fun ctx => { ctx with tacSnap? := ctx.tacSnap?.filter fun tacSnap => Id.run do
    if let some old := tacSnap.old? then
      if cond && opts.getBool `trace.Elab.reuse then
        dbg_trace "reuse stopped: guard failed at {old.stx}"
    return !cond
  }) act

/-- Disables incremental tactic reuse for `act` if `cond` is true. -/
def withoutTacticReuse [Monad m] [MonadWithReaderOf Context m] [MonadOptions m]
    (cond : Bool) (act : m α) : m α := do
  let opts ← getOptions
  withTheReader Term.Context (fun ctx => { ctx with tacSnap? := ctx.tacSnap?.map fun tacSnap =>
    { tacSnap with old? := tacSnap.old?.filter fun old => Id.run do
      if cond && opts.getBool `trace.Elab.reuse then
        dbg_trace "reuse stopped: guard failed at {old.stx}"
      return !cond }
  }) act

abbrev TermElabResult (α : Type) := EStateM.Result Exception SavedState α

/--
  Execute `x`, save resulting expression and new state.
  We remove any `Info` created by `x`.
  The info nodes are committed when we execute `applyResult`.
  We use `observing` to implement overloaded notation and decls.
  We want to save `Info` nodes for the chosen alternative.
-/
def observing (x : TermElabM α) : TermElabM (TermElabResult α) := do
  let s ← saveState
  try
    let e ← x
    let sNew ← saveState
    s.restore (restoreInfo := true)
    return EStateM.Result.ok e sNew
  catch
    | ex@(.error ..) =>
      let sNew ← saveState
      s.restore (restoreInfo := true)
      return .error ex sNew
    | ex@(.internal id _) =>
      if id == postponeExceptionId then
        s.restore (restoreInfo := true)
      throw ex

/--
  Apply the result/exception and state captured with `observing`.
  We use this method to implement overloaded notation and symbols. -/
def applyResult (result : TermElabResult α) : TermElabM α := do
  match result with
  | .ok a r     => r.restore (restoreInfo := true); return a
  | .error ex r => r.restore (restoreInfo := true); throw ex

/--
  Execute `x`, but keep state modifications only if `x` did not postpone.
  This method is useful to implement elaboration functions that cannot decide whether
  they need to postpone or not without updating the state. -/
def commitIfDidNotPostpone (x : TermElabM α) : TermElabM α := do
  -- We just reuse the implementation of `observing` and `applyResult`.
  let r ← observing x
  applyResult r

/--
  Return the universe level names explicitly provided by the user.
-/
def getLevelNames : TermElabM (List Name) :=
  return (← get).levelNames

/--
  Given a free variable `fvar`, return its declaration.
  This function panics if `fvar` is not a free variable.
-/
def getFVarLocalDecl! (fvar : Expr) : TermElabM LocalDecl := do
  match (← getLCtx).find? fvar.fvarId! with
  | some d => pure d
  | none   => unreachable!

instance : AddErrorMessageContext TermElabM where
  add ref msg := do
    let ctx ← read
    let ref := getBetterRef ref ctx.macroStack
    let msg ← addMessageContext msg
    let msg ← addMacroStack msg ctx.macroStack
    pure (ref, msg)

/--
  Execute `x` without storing `Syntax` for recursive applications. See `saveRecAppSyntax` field at `Context`.
-/
def withoutSavingRecAppSyntax (x : TermElabM α) : TermElabM α :=
  withReader (fun ctx => { ctx with saveRecAppSyntax := false }) x

unsafe def mkTermElabAttributeUnsafe (ref : Name) : IO (KeyedDeclsAttribute TermElab) :=
  mkElabAttribute TermElab `builtin_term_elab `term_elab `Lean.Parser.Term `Lean.Elab.Term.TermElab "term" ref

@[implemented_by mkTermElabAttributeUnsafe]
opaque mkTermElabAttribute (ref : Name) : IO (KeyedDeclsAttribute TermElab)

builtin_initialize termElabAttribute : KeyedDeclsAttribute TermElab ← mkTermElabAttribute decl_name%

/--
  Auxiliary datatype for presenting a Lean lvalue modifier.
  We represent an unelaborated lvalue as a `Syntax` (or `Expr`) and `List LVal`.
  Example: `a.foo.1` is represented as the `Syntax` `a` and the list
  `[LVal.fieldName "foo", LVal.fieldIdx 1]`.
-/
inductive LVal where
  | fieldIdx  (ref : Syntax) (i : Nat)
  /-- Field `suffix?` is for producing better error messages because `x.y` may be a field access or a hierarchical/composite name.
  `ref` is the syntax object representing the field. `fullRef` includes the LHS. -/
  | fieldName (ref : Syntax) (name : String) (suffix? : Option Name) (fullRef : Syntax)

def LVal.getRef : LVal → Syntax
  | .fieldIdx ref _    => ref
  | .fieldName ref ..  => ref

def LVal.isFieldName : LVal → Bool
  | .fieldName .. => true
  | _ => false

instance : ToString LVal where
  toString
    | .fieldIdx _ i     => toString i
    | .fieldName _ n .. => n

/-- Return the name of the declaration being elaborated if available. -/
def getDeclName? : TermElabM (Option Name) := return (← read).declName?
/-- Return the list of nested `let rec` declarations that need to be lifted. -/
def getLetRecsToLift : TermElabM (List LetRecToLift) := return (← get).letRecsToLift
/-- Return the declaration of the given metavariable -/
def getMVarDecl (mvarId : MVarId) : TermElabM MetavarDecl := return (← getMCtx).getDecl mvarId

instance : MonadParentDecl TermElabM where
  getParentDeclName? := getDeclName?

/-- Execute `withSaveParentDeclInfoContext x` with `declName? := name`. See `getDeclName?`. -/
def withDeclName (name : Name) (x : TermElabM α) : TermElabM α :=
  withReader (fun ctx => { ctx with declName? := name }) <| withSaveParentDeclInfoContext x

/-- Update the universe level parameter names. -/
def setLevelNames (levelNames : List Name) : TermElabM Unit :=
  modify fun s => { s with levelNames := levelNames }

/-- Execute `x` using `levelNames` as the universe level parameter names. See `getLevelNames`. -/
def withLevelNames (levelNames : List Name) (x : TermElabM α) : TermElabM α := do
  let levelNamesSaved ← getLevelNames
  setLevelNames levelNames
  try x finally setLevelNames levelNamesSaved

/--
  Declare an auxiliary local declaration `shortDeclName : type` for elaborating recursive declaration `declName`,
  update the mapping `auxDeclToFullName`, and then execute `k`.
-/
def withAuxDecl (shortDeclName : Name) (type : Expr) (declName : Name) (k : Expr → TermElabM α) : TermElabM α :=
  withLocalDecl shortDeclName .default (kind := .auxDecl) type fun x =>
    withReader (fun ctx => { ctx with auxDeclToFullName := ctx.auxDeclToFullName.insert x.fvarId! declName }) do
      k x

def withoutErrToSorryImp (x : TermElabM α) : TermElabM α :=
  withReader (fun ctx => { ctx with errToSorry := false }) x

/--
  Execute `x` without converting errors (i.e., exceptions) to `sorry` applications.
  Recall that when `errToSorry = true`, the method `elabTerm` catches exceptions and converts them into `sorry` applications.
-/
def withoutErrToSorry [MonadFunctorT TermElabM m] : m α → m α :=
  monadMap (m := TermElabM) withoutErrToSorryImp

def withoutHeedElabAsElimImp (x : TermElabM α) : TermElabM α :=
  withReader (fun ctx => { ctx with heedElabAsElim := false }) x

/--
  Execute `x` without heeding the `elab_as_elim` attribute. Useful when there is
  no expected type (so `elabAppArgs` would fail), but expect that the user wants
  to use such constants.
-/
def withoutHeedElabAsElim [MonadFunctorT TermElabM m] : m α → m α :=
  monadMap (m := TermElabM) withoutHeedElabAsElimImp

/--
  Execute `x` but discard changes performed at `Term.State` and `Meta.State`.
  Recall that the `Environment` and `InfoState` are at `Core.State`. Thus, any updates to it will
  be preserved. This method is useful for performing computations where all
  metavariable must be resolved or discarded.
  The `InfoTree`s are not discarded, however, and wrapped in `InfoTree.Context`
  to store their metavariable context. -/
def withoutModifyingElabMetaStateWithInfo (x : TermElabM α) : TermElabM α := do
  let s ← get
  let sMeta ← getThe Meta.State
  try
    withSaveInfoContext x
  finally
    set s
    set sMeta

/--
  Execute `x` but discard changes performed to the state.
  However, the info trees and messages are not discarded. -/
private def withoutModifyingStateWithInfoAndMessagesImpl (x : TermElabM α) : TermElabM α := do
  let saved ← saveState
  try
    withSaveInfoContext x
  finally
    let saved := { saved with meta.core.infoState := (← getInfoState), meta.core.messages := (← getThe Core.State).messages }
    restoreState saved

/--
Wraps the trees returned from `getInfoTrees`, if any, in an `InfoTree.context` node based on the
current monadic context and state. This is mainly used to report info trees early via
`Snapshot.infoTree?`. The trees are not removed from the `getInfoTrees` state as the final info tree
of the elaborated command should be complete and not depend on whether parts have been reported
early.

As `InfoTree.context` can have only one child, this function panics if `trees` contains more than 1
tree. Also, `PartialContextInfo.parentDeclCtx` is not currently generated as that information is not
available in the monadic context and only needed for the final info tree.
-/
def getInfoTreeWithContext? : TermElabM (Option InfoTree) := do
  let st ← getInfoState
  if st.trees.size > 1 then
    return panic! "getInfoTreeWithContext: overfull tree"
  let some t := st.trees[0]? |
    return none
  let t := t.substitute st.assignment
  let ctx ← readThe Core.Context
  let s ← getThe Core.State
  let ctx := PartialContextInfo.commandCtx {
    env := s.env, fileMap := ctx.fileMap, mctx := {}, currNamespace := ctx.currNamespace,
    openDecls := ctx.openDecls, options := ctx.options, ngen := s.ngen
  }
  return InfoTree.context ctx t

/-- For testing `TermElabM` methods. The #eval command will sign the error. -/
def throwErrorIfErrors : TermElabM Unit := do
  if (← MonadLog.hasErrors) then
    throwError "Error(s)"

def traceAtCmdPos (cls : Name) (msg : Unit → MessageData) : TermElabM Unit :=
  withRef Syntax.missing <| trace cls msg

def ppGoal (mvarId : MVarId) : TermElabM Format :=
  Meta.ppGoal mvarId

open Level (LevelElabM)

def liftLevelM (x : LevelElabM α) : TermElabM α := do
  let ctx ← read
  let mctx ← getMCtx
  let ngen ← getNGen
  let lvlCtx : Level.Context := { options := (← getOptions), ref := (← getRef), autoBoundImplicit := ctx.autoBoundImplicit }
  match (x lvlCtx).run { ngen := ngen, mctx := mctx, levelNames := (← getLevelNames) } with
  | .ok a newS  => setMCtx newS.mctx; setNGen newS.ngen; setLevelNames newS.levelNames; pure a
  | .error ex _ => throw ex

def elabLevel (stx : Syntax) : TermElabM Level :=
  liftLevelM <| Level.elabLevel stx

/-- Elaborate `x` with `stx` on the macro stack -/
def withPushMacroExpansionStack (beforeStx afterStx : Syntax) (x : TermElabM α) : TermElabM α :=
  withReader (fun ctx => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

/-- Elaborate `x` with `stx` on the macro stack and produce macro expansion info -/
def withMacroExpansion (beforeStx afterStx : Syntax) (x : TermElabM α) : TermElabM α :=
  withMacroExpansionInfo beforeStx afterStx do
    withPushMacroExpansionStack beforeStx afterStx x

/--
  Add the given metavariable to the list of pending synthetic metavariables.
  The method `synthesizeSyntheticMVars` is used to process the metavariables on this list. -/
def registerSyntheticMVar (stx : Syntax) (mvarId : MVarId) (kind : SyntheticMVarKind) : TermElabM Unit := do
  modify fun s => { s with syntheticMVars := s.syntheticMVars.insert mvarId { stx, kind }, pendingMVars := mvarId :: s.pendingMVars }

def registerSyntheticMVarWithCurrRef (mvarId : MVarId) (kind : SyntheticMVarKind) : TermElabM Unit := do
  registerSyntheticMVar (← getRef) mvarId kind

def registerMVarErrorInfo (mvarErrorInfo : MVarErrorInfo) : TermElabM Unit :=
  modify fun s => { s with mvarErrorInfos := mvarErrorInfo :: s.mvarErrorInfos }

def registerMVarErrorHoleInfo (mvarId : MVarId) (ref : Syntax) : TermElabM Unit :=
  registerMVarErrorInfo { mvarId, ref, kind := .hole }

def registerMVarErrorImplicitArgInfo (mvarId : MVarId) (ref : Syntax) (app : Expr) : TermElabM Unit := do
  registerMVarErrorInfo { mvarId, ref, kind := .implicitArg (← getLCtx) app }

def registerMVarErrorCustomInfo (mvarId : MVarId) (ref : Syntax) (msgData : MessageData) : TermElabM Unit := do
  registerMVarErrorInfo { mvarId, ref, kind := .custom msgData }

def registerCustomErrorIfMVar (e : Expr) (ref : Syntax) (msgData : MessageData) : TermElabM Unit :=
  match e.getAppFn with
  | Expr.mvar mvarId => registerMVarErrorCustomInfo mvarId ref msgData
  | _ => pure ()

def registerMVarArgName (mvarId : MVarId) (argName : Name) : TermElabM Unit :=
  modify fun s => { s with mvarArgNames := s.mvarArgNames.insert mvarId argName }

/--
  Auxiliary method for reporting errors of the form "... contains metavariables ...".
  This kind of error is thrown, for example, at `Match.lean` where elaboration
  cannot continue if there are metavariables in patterns.
  We only want to log it if we haven't logged any errors so far. -/
def throwMVarError (m : MessageData) : TermElabM α := do
  if (← MonadLog.hasErrors) then
    throwAbortTerm
  else
    throwError m

def MVarErrorInfo.logError (mvarErrorInfo : MVarErrorInfo) (extraMsg? : Option MessageData) : TermElabM Unit := do
  match mvarErrorInfo.kind with
  | MVarErrorKind.implicitArg lctx app => withLCtx lctx {} do
    let app ← instantiateMVars app
    let msg ← addArgName "don't know how to synthesize implicit argument"
    let msg := msg ++ m!"{indentExpr app.setAppPPExplicitForExposingMVars}" ++ Format.line ++ "context:" ++ Format.line ++ MessageData.ofGoal mvarErrorInfo.mvarId
    logErrorAt mvarErrorInfo.ref (appendExtra msg)
  | MVarErrorKind.hole => do
    let msg ← addArgName "don't know how to synthesize placeholder" " for argument"
    let msg := msg ++ Format.line ++ "context:" ++ Format.line ++ MessageData.ofGoal mvarErrorInfo.mvarId
    logErrorAt mvarErrorInfo.ref (MessageData.tagged `Elab.synthPlaceholder <| appendExtra msg)
  | MVarErrorKind.custom msg =>
    logErrorAt mvarErrorInfo.ref (appendExtra msg)
where
  /-- Append the argument name (if available) to the message.
      Remark: if the argument name contains macro scopes we do not append it. -/
  addArgName (msg : MessageData) (extra : String := "") : TermElabM MessageData := do
    match (← get).mvarArgNames.find? mvarErrorInfo.mvarId with
    | none => return msg
    | some argName => return if argName.hasMacroScopes then msg else msg ++ extra ++ m!" '{argName}'"

  appendExtra (msg : MessageData) : MessageData :=
    match extraMsg? with
    | none => msg
    | some extraMsg => msg ++ extraMsg

/--
  Try to log errors for the unassigned metavariables `pendingMVarIds`.

  Return `true` if there were "unfilled holes", and we should "abort" declaration.
  TODO: try to fill "all" holes using synthetic "sorry's"

  Remark: We only log the "unfilled holes" as new errors if no error has been logged so far. -/
def logUnassignedUsingErrorInfos (pendingMVarIds : Array MVarId) (extraMsg? : Option MessageData := none) : TermElabM Bool := do
  if pendingMVarIds.isEmpty then
    return false
  else
    let hasOtherErrors ← MonadLog.hasErrors
    let mut hasNewErrors := false
    let mut alreadyVisited : MVarIdSet := {}
    let mut errors : Array MVarErrorInfo := #[]
    for mvarErrorInfo in (← get).mvarErrorInfos do
      let mvarId := mvarErrorInfo.mvarId
      unless alreadyVisited.contains mvarId do
        alreadyVisited := alreadyVisited.insert mvarId
        /- The metavariable `mvarErrorInfo.mvarId` may have been assigned or
           delayed assigned to another metavariable that is unassigned. -/
        let mvarDeps ← getMVars (mkMVar mvarId)
        if mvarDeps.any pendingMVarIds.contains then do
          unless hasOtherErrors do
            errors := errors.push mvarErrorInfo
          hasNewErrors := true
    -- To sort the errors by position use
    -- let sortedErrors := errors.qsort fun e₁ e₂ => e₁.ref.getPos?.getD 0 < e₂.ref.getPos?.getD 0
    for error in errors do
      error.mvarId.withContext do
        error.logError extraMsg?
    return hasNewErrors

def registerLevelMVarErrorInfo (levelMVarErrorInfo : LevelMVarErrorInfo) : TermElabM Unit :=
  modify fun s => { s with levelMVarErrorInfos := levelMVarErrorInfo :: s.levelMVarErrorInfos }

def registerLevelMVarErrorExprInfo (expr : Expr) (ref : Syntax) (msgData? : Option MessageData := none) : TermElabM Unit := do
  registerLevelMVarErrorInfo { lctx := (← getLCtx), expr, ref, msgData? }

def exposeLevelMVars (e : Expr) : MetaM Expr :=
  Core.transform e
    (post := fun e => do
      match e with
      | .const _ us     => return .done <| if us.any (·.isMVar) then e.setPPUniverses true else e
      | .sort u         => return .done <| if u.isMVar then e.setPPUniverses true else e
      | .lam _ t _ _    => return .done <| if t.hasLevelMVar then e.setOption `pp.funBinderTypes true else e
      | .letE _ t _ _ _ => return .done <| if t.hasLevelMVar then e.setOption `pp.letVarTypes true else e
      | _               => return .done e)

def LevelMVarErrorInfo.logError (levelMVarErrorInfo : LevelMVarErrorInfo) : TermElabM Unit :=
  Meta.withLCtx levelMVarErrorInfo.lctx {} do
    let e' ← exposeLevelMVars (← instantiateMVars levelMVarErrorInfo.expr)
    let msg := levelMVarErrorInfo.msgData?.getD m!"don't know how to synthesize universe level metavariables"
    let msg := m!"{msg}{indentExpr e'}"
    logErrorAt levelMVarErrorInfo.ref msg

/--
Try to log errors for unassigned level metavariables `pendingLevelMVarIds`.

Returns `true` if there are any relevant `LevelMVarErrorInfo`s and we should "abort" the declaration.

Remark: we only log unassigned level metavariables as new errors if no error has been logged so far.
-/
def logUnassignedLevelMVarsUsingErrorInfos (pendingLevelMVarIds : Array LMVarId) : TermElabM Bool := do
  if pendingLevelMVarIds.isEmpty then
    return false
  else
    let hasOtherErrors ← MonadLog.hasErrors
    let mut hasNewErrors := false
    let mut errors : Array LevelMVarErrorInfo := #[]
    for levelMVarErrorInfo in (← get).levelMVarErrorInfos do
      let e ← instantiateMVars levelMVarErrorInfo.expr
      let lmvars := (collectLevelMVars {} e).result
      if lmvars.any pendingLevelMVarIds.contains then do
        unless hasOtherErrors do
          errors := errors.push levelMVarErrorInfo
        hasNewErrors := true
    for error in errors do
      error.logError
    return hasNewErrors

/-- Ensure metavariables registered using `registerMVarErrorInfos` (and used in the given declaration) have been assigned. -/
def ensureNoUnassignedMVars (decl : Declaration) : TermElabM Unit := do
  let pendingMVarIds ← getMVarsAtDecl decl
  if (← logUnassignedUsingErrorInfos pendingMVarIds) then
    throwAbortCommand

/--
  Execute `x` without allowing it to postpone elaboration tasks.
  That is, `tryPostpone` is a noop. -/
def withoutPostponing (x : TermElabM α) : TermElabM α :=
  withReader (fun ctx => { ctx with mayPostpone := false }) x

/-- Creates syntax for `(` <ident> `:` <type> `)` -/
def mkExplicitBinder (ident : Syntax) (type : Syntax) : Syntax :=
  mkNode ``Lean.Parser.Term.explicitBinder #[mkAtom "(", mkNullNode #[ident], mkNullNode #[mkAtom ":", type], mkNullNode, mkAtom ")"]

/--
  Convert unassigned universe level metavariables into parameters.
  The new parameter names are fresh names of the form `u_i` with regard to `ctx.levelNames`, which is updated with the new names. -/
def levelMVarToParam (e : Expr) (except : LMVarId → Bool := fun _ => false) : TermElabM Expr := do
  let levelNames ← getLevelNames
  let r := (← getMCtx).levelMVarToParam (fun n => levelNames.elem n) except e `u 1
  -- Recall that the most recent universe is the first element of the field `levelNames`.
  setLevelNames (r.newParamNames.reverse.toList ++ levelNames)
  setMCtx r.mctx
  return r.expr

/--
  Auxiliary method for creating fresh binder names.
  Do not confuse with the method for creating fresh free/meta variable ids. -/
def mkFreshBinderName [Monad m] [MonadQuotation m] : m Name :=
  withFreshMacroScope <| MonadQuotation.addMacroScope `x

/--
  Auxiliary method for creating a `Syntax.ident` containing
  a fresh name. This method is intended for creating fresh binder names.
  It is just a thin layer on top of `mkFreshUserName`. -/
def mkFreshIdent [Monad m] [MonadQuotation m] (ref : Syntax) (canonical := false) : m Ident :=
  return mkIdentFrom ref (← mkFreshBinderName) canonical

private def applyAttributesCore
    (declName : Name) (attrs : Array Attribute)
    (applicationTime? : Option AttributeApplicationTime) : TermElabM Unit := do profileitM Exception "attribute application" (← getOptions) do
  /-
  Remark: if the declaration has syntax errors, `declName` may be `.anonymous` see issue #4309
  In this case, we skip attribute application.
  -/
  if declName == .anonymous then
    return
  withDeclName declName do
    for attr in attrs do
      withRef attr.stx do withLogging do
      let env ← getEnv
      match getAttributeImpl env attr.name with
      | Except.error errMsg => throwError errMsg
      | Except.ok attrImpl  =>
        let runAttr := attrImpl.add declName attr.stx attr.kind
        let runAttr := do
          -- not truly an elaborator, but a sensible target for go-to-definition
          let elaborator := attrImpl.ref
          if (← getInfoState).enabled && (← getEnv).contains elaborator then
            withInfoContext (mkInfo := return .ofCommandInfo { elaborator, stx := attr.stx }) do
              try runAttr
              finally if attr.stx[0].isIdent || attr.stx[0].isAtom then
                -- Add an additional node over the leading identifier if there is one to make it look more function-like.
                -- Do this last because we want user-created infos to take precedence
                pushInfoLeaf <| .ofCommandInfo { elaborator, stx := attr.stx[0] }
          else
            runAttr
        match applicationTime? with
        | none => runAttr
        | some applicationTime =>
          if applicationTime == attrImpl.applicationTime then
            runAttr

/-- Apply given attributes **at** a given application time -/
def applyAttributesAt (declName : Name) (attrs : Array Attribute) (applicationTime : AttributeApplicationTime) : TermElabM Unit :=
  applyAttributesCore declName attrs applicationTime

def applyAttributes (declName : Name) (attrs : Array Attribute) : TermElabM Unit :=
  applyAttributesCore declName attrs none

def mkTypeMismatchError (header? : Option MessageData) (e : Expr) (eType : Expr) (expectedType : Expr) : MetaM MessageData := do
  let header : MessageData := match header? with
    | some header => m!"{header} "
    | none        => m!"type mismatch{indentExpr e}\n"
  return m!"{header}{← mkHasTypeButIsExpectedMsg eType expectedType}"

def throwTypeMismatchError (header? : Option MessageData) (expectedType : Expr) (eType : Expr) (e : Expr)
    (f? : Option Expr := none) (_extraMsg? : Option MessageData := none) : MetaM α := do
  /-
    We ignore `extraMsg?` for now. In all our tests, it contained no useful information. It was
    always of the form:
    ```
    failed to synthesize instance
      CoeT <eType> <e> <expectedType>
    ```
    We should revisit this decision in the future and decide whether it may contain useful information
    or not. -/
  let extraMsg := Format.nil
  /-
  let extraMsg : MessageData := match extraMsg? with
    | none          => Format.nil
    | some extraMsg => Format.line ++ extraMsg;
  -/
  match f? with
  | none   => throwError "{← mkTypeMismatchError header? e eType expectedType}{extraMsg}"
  | some f => Meta.throwAppTypeMismatch f e

def withoutMacroStackAtErr (x : TermElabM α) : TermElabM α :=
  withTheReader Core.Context (fun (ctx : Core.Context) => { ctx with options := pp.macroStack.set ctx.options false }) x

namespace ContainsPendingMVar

abbrev M := MonadCacheT Expr Unit (OptionT MetaM)

/-- See `containsPostponedTerm` -/
partial def visit (e : Expr) : M Unit := do
  checkCache e fun _ => do
    match e with
    | .forallE _ d b _   => visit d; visit b
    | .lam _ d b _       => visit d; visit b
    | .letE _ t v b _    => visit t; visit v; visit b
    | .app f a           => visit f; visit a
    | .mdata _ b         => visit b
    | .proj _ _ b        => visit b
    | .fvar fvarId ..    =>
      match (← fvarId.getDecl) with
      | .cdecl .. => return ()
      | .ldecl (value := v) .. => visit v
    | .mvar mvarId ..    =>
      let e' ← instantiateMVars e
      if e' != e then
        visit e'
      else
        match (← getDelayedMVarAssignment? mvarId) with
        | some d => visit (mkMVar d.mvarIdPending)
        | none   => failure
    | _ => return ()

end ContainsPendingMVar

/-- Return `true` if `e` contains a pending metavariable. Remark: it also visits let-declarations. -/
def containsPendingMVar (e : Expr) : MetaM Bool := do
  match (← ContainsPendingMVar.visit e |>.run.run) with
  | some _ => return false
  | none   => return true

/--
  Try to synthesize metavariable using type class resolution.
  This method assumes the local context and local instances of `instMVar` coincide
  with the current local context and local instances.
  Return `true` if the instance was synthesized successfully, and `false` if
  the instance contains unassigned metavariables that are blocking the type class
  resolution procedure. Throw an exception if resolution or assignment irrevocably fails.

  If `extraErrorMsg?` is not none, it contains additional information that should be attached
  to type class synthesis failures.
-/
def synthesizeInstMVarCore (instMVar : MVarId) (maxResultSize? : Option Nat := none) (extraErrorMsg? : Option MessageData := none): TermElabM Bool := do
  let extraErrorMsg := extraMsgToMsg extraErrorMsg?
  let instMVarDecl ← getMVarDecl instMVar
  let type := instMVarDecl.type
  let type ← instantiateMVars type
  let result ← trySynthInstance type maxResultSize?
  match result with
  | LOption.some val =>
    if (← instMVar.isAssigned) then
      let oldVal ← instantiateMVars (mkMVar instMVar)
      unless (← isDefEq oldVal val) do
        if (← containsPendingMVar oldVal <||> containsPendingMVar val) then
          /- If `val` or `oldVal` contains metavariables directly or indirectly (e.g., in a let-declaration),
             we return `false` to indicate we should try again later. This is very coarse grain since
             the metavariable may not be responsible for the failure. We should refine the test in the future if needed.
             This check has been added to address dependencies between postponed metavariables. The following
             example demonstrates the issue fixed by this test.
             ```
               structure Point where
                 x : Nat
                 y : Nat

               def Point.compute (p : Point) : Point :=
                 let p := { p with x := 1 }
                 let p := { p with y := 0 }
                 if (p.x - p.y) > p.x then p else p
             ```
             The `isDefEq` test above fails for `Decidable (p.x - p.y ≤ p.x)` when the structure instance assigned to
             `p` has not been elaborated yet.
           -/
          return false -- we will try again later
        let oldValType ← inferType oldVal
        let valType ← inferType val
        unless (← isDefEq oldValType valType) do
          throwError "synthesized type class instance type is not definitionally equal to expected type, synthesized{indentExpr val}\nhas type{indentExpr valType}\nexpected{indentExpr oldValType}{extraErrorMsg}"
        throwError "synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized{indentExpr val}\ninferred{indentExpr oldVal}{extraErrorMsg}"
    else
      unless (← isDefEq (mkMVar instMVar) val) do
        throwError "failed to assign synthesized type class instance{indentExpr val}{extraErrorMsg}"
    return true
  | .undef => return false -- we will try later
  | .none  =>
    if (← read).ignoreTCFailures then
      return false
    else
      throwError "failed to synthesize{indentExpr type}{extraErrorMsg}{useDiagnosticMsg}"

def mkCoe (expectedType : Expr) (e : Expr) (f? : Option Expr := none) (errorMsgHeader? : Option String := none)
    (mkErrorMsg? : Option (MVarId → (expectedType e : Expr) → MetaM MessageData) := none)
    (mkImmedErrorMsg? : Option ((errorMsg? : Option MessageData) → (expectedType e : Expr) → MetaM MessageData) := none) : TermElabM Expr := do
  withTraceNode `Elab.coe (fun _ => return m!"adding coercion for {e} : {← inferType e} =?= {expectedType}") do
  try
    withoutMacroStackAtErr do
      match ← coerce? e expectedType with
      | .some eNew => return eNew
      | .none => failure
      | .undef =>
        let mvarAux ← mkFreshExprMVar expectedType MetavarKind.syntheticOpaque
        registerSyntheticMVarWithCurrRef mvarAux.mvarId! (.coe errorMsgHeader? expectedType e f? mkErrorMsg?)
        return mvarAux
  catch
    | .error _ msg =>
      if let some mkImmedErrorMsg := mkImmedErrorMsg? then
        throwError (← mkImmedErrorMsg msg expectedType e)
      else
        throwTypeMismatchError errorMsgHeader? expectedType (← inferType e) e f? msg
    | _            =>
      if let some mkImmedErrorMsg := mkImmedErrorMsg? then
        throwError (← mkImmedErrorMsg none expectedType e)
      else
        throwTypeMismatchError errorMsgHeader? expectedType (← inferType e) e f?

def mkCoeWithErrorMsgs (expectedType : Expr) (e : Expr)
    (mkImmedErrorMsg : (errorMsg? : Option MessageData) → (expectedType e : Expr) → MetaM MessageData)
    (mkErrorMsg : MVarId → (expectedType e : Expr) → MetaM MessageData) : TermElabM Expr := do
  mkCoe expectedType e (mkImmedErrorMsg? := mkImmedErrorMsg) (mkErrorMsg? := mkErrorMsg)

/--
If `expectedType?` is `some t`, then ensures `t` and `eType` are definitionally equal by inserting a coercion if necessary.

Argument `f?` is used only for generating error messages when inserting coercions fails.
-/
def ensureHasType (expectedType? : Option Expr) (e : Expr)
    (errorMsgHeader? : Option String := none) (f? : Option Expr := none) : TermElabM Expr := do
  let some expectedType := expectedType? | return e
  if (← isDefEq (← inferType e) expectedType) then
    return e
  else
    mkCoe expectedType e f? errorMsgHeader?

def ensureHasTypeWithErrorMsgs (expectedType? : Option Expr) (e : Expr)
    (mkImmedErrorMsg : (errorMsg? : Option MessageData) → (expectedType e : Expr) → MetaM MessageData)
    (mkErrorMsg : MVarId → (expectedType e : Expr) → MetaM MessageData) : TermElabM Expr := do
  let some expectedType := expectedType? | return e
  if (← isDefEq (← inferType e) expectedType) then
    return e
  else
    mkCoeWithErrorMsgs expectedType e mkImmedErrorMsg mkErrorMsg

/--
  Create a synthetic sorry for the given expected type. If `expectedType? = none`, then a fresh
  metavariable is created to represent the type.
-/
private def mkSyntheticSorryFor (expectedType? : Option Expr) : TermElabM Expr := do
  let expectedType ← match expectedType? with
    | none              => mkFreshTypeMVar
    | some expectedType => pure expectedType
  mkSyntheticSorry expectedType

/--
  Log the given exception, and create a synthetic sorry for representing the failed
  elaboration step with exception `ex`.
-/
def exceptionToSorry (ex : Exception) (expectedType? : Option Expr) : TermElabM Expr := do
  let syntheticSorry ← mkSyntheticSorryFor expectedType?
  logException ex
  pure syntheticSorry

/-- If `mayPostpone == true`, throw `Exception.postpone`. -/
def tryPostpone : TermElabM Unit := do
  if (← read).mayPostpone then
    throwPostpone

/-- Return `true` if `e` reduces (by unfolding only `[reducible]` declarations) to `?m ...` -/
def isMVarApp (e : Expr) : TermElabM Bool :=
  return (← whnfR e).getAppFn.isMVar

/-- If `mayPostpone == true` and `e`'s head is a metavariable, throw `Exception.postpone`. -/
def tryPostponeIfMVar (e : Expr) : TermElabM Unit := do
  if (← isMVarApp e) then
    tryPostpone

/-- If `e? = some e`, then `tryPostponeIfMVar e`, otherwise it is just `tryPostpone`. -/
def tryPostponeIfNoneOrMVar (e? : Option Expr) : TermElabM Unit :=
  match e? with
  | some e => tryPostponeIfMVar e
  | none   => tryPostpone

/--
  Throws `Exception.postpone`, if `expectedType?` contains unassigned metavariables.
  It is a noop if `mayPostpone == false`.
-/
def tryPostponeIfHasMVars? (expectedType? : Option Expr) : TermElabM (Option Expr) := do
  tryPostponeIfNoneOrMVar expectedType?
  let some expectedType := expectedType? | return none
  let expectedType ← instantiateMVars expectedType
  if expectedType.hasExprMVar then
    tryPostpone
    return none
  return some expectedType

/--
  Throws `Exception.postpone`, if `expectedType?` contains unassigned metavariables.
  If `mayPostpone == false`, it throws error `msg`.
-/
def tryPostponeIfHasMVars (expectedType? : Option Expr) (msg : String) : TermElabM Expr := do
  let some expectedType ← tryPostponeIfHasMVars? expectedType? |
    throwError "{msg}, expected type contains metavariables{indentD expectedType?}"
  return expectedType

def withExpectedType (expectedType? : Option Expr) (x : Expr → TermElabM Expr) : TermElabM Expr := do
  tryPostponeIfNoneOrMVar expectedType?
  let some expectedType ← pure expectedType?
    | throwError "expected type must be known"
  x expectedType

/--
  Save relevant context for term elaboration postponement.
-/
def saveContext : TermElabM SavedContext :=
  return {
    macroStack := (← read).macroStack
    declName?  := (← read).declName?
    options    := (← getOptions)
    openDecls  := (← getOpenDecls)
    errToSorry := (← read).errToSorry
    levelNames := (← get).levelNames
  }

/--
  Execute `x` with the context saved using `saveContext`.
-/
def withSavedContext (savedCtx : SavedContext) (x : TermElabM α) : TermElabM α := do
  withReader (fun ctx => { ctx with declName? := savedCtx.declName?, macroStack := savedCtx.macroStack, errToSorry := savedCtx.errToSorry }) <|
    withTheReader Core.Context (fun ctx => { ctx with options := savedCtx.options, openDecls := savedCtx.openDecls }) <|
      withLevelNames savedCtx.levelNames x

/--
Delay the elaboration of `stx`, and return a fresh metavariable that works a placeholder.
Remark: the caller is responsible for making sure the info tree is properly updated.
This method is used only at `elabUsingElabFnsAux`.
-/
private def postponeElabTermCore (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  trace[Elab.postpone] "{stx} : {expectedType?}"
  let mvar ← mkFreshExprMVar expectedType? MetavarKind.syntheticOpaque
  registerSyntheticMVar stx mvar.mvarId! (SyntheticMVarKind.postponed (← saveContext))
  return mvar

def getSyntheticMVarDecl? (mvarId : MVarId) : TermElabM (Option SyntheticMVarDecl) :=
  return (← get).syntheticMVars.find? mvarId

register_builtin_option debug.byAsSorry : Bool := {
  defValue := false
  group    := "debug"
  descr    := "replace `by ..` blocks with `sorry` IF the expected type is a proposition"
}

/--
Creates a new metavariable of type `type` that will be synthesized using the tactic code.
The `tacticCode` syntax is the full `by ..` syntax.
-/
def mkTacticMVar (type : Expr) (tacticCode : Syntax) (kind : TacticMVarKind) : TermElabM Expr := do
  if ← pure (debug.byAsSorry.get (← getOptions)) <&&> isProp type then
    mkSorry type false
  else
    let mvar ← mkFreshExprMVar type MetavarKind.syntheticOpaque
    let mvarId := mvar.mvarId!
    let ref ← getRef
    registerSyntheticMVar ref mvarId <| SyntheticMVarKind.tactic tacticCode (← saveContext) kind
    return mvar

/--
  Create an auxiliary annotation to make sure we create an `Info` even if `e` is a metavariable.
  See `mkTermInfo`.

  We use this function because some elaboration functions elaborate subterms that may not be immediately
  part of the resulting term. Example:
  ```
  let_mvar% ?m := b; wait_if_type_mvar% ?m; body
  ```
  If the type of `b` is not known, then `wait_if_type_mvar% ?m; body` is postponed and just returns a fresh
  metavariable `?n`. The elaborator for
  ```
  let_mvar% ?m := b; wait_if_type_mvar% ?m; body
  ```
  returns `mkSaveInfoAnnotation ?n` to make sure the info nodes created when elaborating `b` are "saved".
  This is a bit hackish, but elaborators like `let_mvar%` are rare.
-/
def mkSaveInfoAnnotation (e : Expr) : Expr :=
  if e.isMVar then
    mkAnnotation `save_info e
  else
    e

def isSaveInfoAnnotation? (e : Expr) : Option Expr :=
  annotation? `save_info e

partial def removeSaveInfoAnnotation (e : Expr) : Expr :=
  match isSaveInfoAnnotation? e with
  | some e => removeSaveInfoAnnotation e
  | _ => e

/--
  Return `some mvarId` if `e` corresponds to a hole that is going to be filled "later" by executing a tactic or resuming elaboration.

  We do not save `ofTermInfo` for this kind of node in the `InfoTree`.
-/
def isTacticOrPostponedHole? (e : Expr) : TermElabM (Option MVarId) := do
  match e with
  | Expr.mvar mvarId =>
    match (← getSyntheticMVarDecl? mvarId) with
    | some { kind := .tactic .., .. }    => return mvarId
    | some { kind := .postponed .., .. } => return mvarId
    | _                                  => return none
  | _ => pure none

def mkTermInfo (elaborator : Name) (stx : Syntax) (e : Expr) (expectedType? : Option Expr := none) (lctx? : Option LocalContext := none) (isBinder := false) : TermElabM (Sum Info MVarId) := do
  match (← isTacticOrPostponedHole? e) with
  | some mvarId => return Sum.inr mvarId
  | none =>
    let e := removeSaveInfoAnnotation e
    return Sum.inl <| Info.ofTermInfo { elaborator, lctx := lctx?.getD (← getLCtx), expr := e, stx, expectedType?, isBinder }

/--
Pushes a new leaf node to the info tree associating the expression `e` to the syntax `stx`.
As a result, when the user hovers over `stx` they will see the type of `e`, and if `e`
is a constant they will see the constant's doc string.

* `expectedType?`: the expected type of `e` at the point of elaboration, if available
* `lctx?`: the local context in which to interpret `e` (otherwise it will use `← getLCtx`)
* `elaborator`: a declaration name used as an alternative target for go-to-definition
* `isBinder`: if true, this will be treated as defining `e` (which should be a local constant)
  for the purpose of go-to-definition on local variables
* `force`: In patterns, the effect of `addTermInfo` is usually suppressed and replaced
  by a `patternWithRef?` annotation which will be turned into a term info on the
  post-match-elaboration expression. This flag overrides that behavior and adds the term
  info immediately. (See https://github.com/leanprover/lean4/pull/1664.)
-/
def addTermInfo (stx : Syntax) (e : Expr) (expectedType? : Option Expr := none)
    (lctx? : Option LocalContext := none) (elaborator := Name.anonymous)
    (isBinder := false) (force := false) : TermElabM Expr := do
  if (← read).inPattern && !force then
    return mkPatternWithRef e stx
  else
    withInfoContext' (pure ()) (fun _ => mkTermInfo elaborator stx e expectedType? lctx? isBinder) |> discard
    return e

def addTermInfo' (stx : Syntax) (e : Expr) (expectedType? : Option Expr := none) (lctx? : Option LocalContext := none) (elaborator := Name.anonymous) (isBinder := false) : TermElabM Unit :=
  discard <| addTermInfo stx e expectedType? lctx? elaborator isBinder

def withInfoContext' (stx : Syntax) (x : TermElabM Expr) (mkInfo : Expr → TermElabM (Sum Info MVarId)) : TermElabM Expr := do
  if (← read).inPattern then
    let e ← x
    return mkPatternWithRef e stx
  else
    Elab.withInfoContext' x mkInfo

/-- Info node capturing `def/let rec` bodies, used by the unused variables linter. -/
structure BodyInfo where
  /-- The body as a fully elaborated term. -/
  value : Expr
deriving TypeName

/-- Creates an `Info.ofCustomInfo` node backed by a `BodyInfo`. -/
def mkBodyInfo (stx : Syntax) (value : Expr) : Info :=
  .ofCustomInfo { stx, value := .mk { value : BodyInfo } }

/-- Extracts a `BodyInfo` custom info. -/
def getBodyInfo? : Info → Option BodyInfo
  | .ofCustomInfo { value, .. } => value.get? BodyInfo
  | _ => none

/--
Postpone the elaboration of `stx`, return a metavariable that acts as a placeholder, and
ensures the info tree is updated and a hole id is introduced.
When `stx` is elaborated, new info nodes are created and attached to the new hole id in the info tree.
-/
def postponeElabTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  withInfoContext' stx (mkInfo := mkTermInfo .anonymous (expectedType? := expectedType?) stx) do
    postponeElabTermCore stx expectedType?

/--
  Helper function for `elabTerm` that tries the registered elaboration functions for `stxNode` kind until it finds one that supports the syntax or
  an error is found. -/
private def elabUsingElabFnsAux (s : SavedState) (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone : Bool)
    : List (KeyedDeclsAttribute.AttributeEntry TermElab) → TermElabM Expr
  | []                => do throwError "unexpected syntax{indentD stx}"
  | (elabFn::elabFns) =>
    try
      -- record elaborator in info tree, but only when not backtracking to other elaborators (outer `try`)
      withInfoContext' stx (mkInfo := mkTermInfo elabFn.declName (expectedType? := expectedType?) stx)
        (try
          elabFn.value stx expectedType?
        catch ex => match ex with
          | .error .. =>
            if (← read).errToSorry then
              exceptionToSorry ex expectedType?
            else
              throw ex
          | .internal id _ =>
            if (← read).errToSorry && id == abortTermExceptionId then
              exceptionToSorry ex expectedType?
            else if id == unsupportedSyntaxExceptionId then
              throw ex  -- to outer try
            else if catchExPostpone && id == postponeExceptionId then
              /- If `elab` threw `Exception.postpone`, we reset any state modifications.
                For example, we want to make sure pending synthetic metavariables created by `elab` before
                it threw `Exception.postpone` are discarded.
                Note that we are also discarding the messages created by `elab`.

                For example, consider the expression.
                `((f.x a1).x a2).x a3`
                Now, suppose the elaboration of `f.x a1` produces an `Exception.postpone`.
                Then, a new metavariable `?m` is created. Then, `?m.x a2` also throws `Exception.postpone`
                because the type of `?m` is not yet known. Then another, metavariable `?n` is created, and
                finally `?n.x a3` also throws `Exception.postpone`. If we did not restore the state, we would
                keep "dead" metavariables `?m` and `?n` on the pending synthetic metavariable list. This is
                wasteful because when we resume the elaboration of `((f.x a1).x a2).x a3`, we start it from scratch
                and new metavariables are created for the nested functions. -/
              s.restore
              postponeElabTermCore stx expectedType?
            else
              throw ex)
    catch ex => match ex with
      | .internal id _ =>
        if id == unsupportedSyntaxExceptionId then
          s.restore  -- also removes the info tree created above
          elabUsingElabFnsAux s stx expectedType? catchExPostpone elabFns
        else
          throw ex
      | _ => throw ex

private def elabUsingElabFns (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone : Bool) : TermElabM Expr := do
  let s ← saveState
  let k := stx.getKind
  match termElabAttribute.getEntries (← getEnv) k with
  | []      => throwError "elaboration function for '{k}' has not been implemented{indentD stx}"
  | elabFns => elabUsingElabFnsAux s stx expectedType? catchExPostpone elabFns

instance : MonadMacroAdapter TermElabM where
  getCurrMacroScope := getCurrMacroScope
  getNextMacroScope := return (← getThe Core.State).nextMacroScope
  setNextMacroScope next := modifyThe Core.State fun s => { s with nextMacroScope := next }

private def isExplicit (stx : Syntax) : Bool :=
  match stx with
  | `(@$_) => true
  | _      => false

private def isExplicitApp (stx : Syntax) : Bool :=
  stx.getKind == ``Lean.Parser.Term.app && isExplicit stx[0]

/--
  Return true if `stx` is a lambda abstraction containing a `{}` or `[]` binder annotation.
  Example: `fun {α} (a : α) => a` -/
private def isLambdaWithImplicit (stx : Syntax) : Bool :=
  match stx with
  | `(fun $binders* => $_) => binders.raw.any fun b => b.isOfKind ``Lean.Parser.Term.implicitBinder || b.isOfKind `Lean.Parser.Term.instBinder
  | _                      => false

private partial def dropTermParens : Syntax → Syntax := fun stx =>
  match stx with
  | `(($stx)) => dropTermParens stx
  | _         => stx

private def isHole (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Term.hole || stx.isOfKind ``Lean.Parser.Term.syntheticHole

private def isTacticBlock (stx : Syntax) : Bool :=
  match stx with
  | `(by $_:tacticSeq) => true
  | _ => false

private def isNoImplicitLambda (stx : Syntax) : Bool :=
  match stx with
  | `(no_implicit_lambda% $_:term) => true
  | _ => false

private def isTypeAscription (stx : Syntax) : Bool :=
  match stx with
  | `(($_ : $[$_]?)) => true
  | _                => false

def hasNoImplicitLambdaAnnotation (type : Expr) : Bool :=
  annotation? `noImplicitLambda type |>.isSome

def mkNoImplicitLambdaAnnotation (type : Expr) : Expr :=
  if hasNoImplicitLambdaAnnotation type then
    type
  else
    mkAnnotation `noImplicitLambda type

/-- Block usage of implicit lambdas if `stx` is `@f` or `@f arg1 ...` or `fun` with an implicit binder annotation. -/
def blockImplicitLambda (stx : Syntax) : Bool :=
  let stx := dropTermParens stx
  -- TODO: make it extensible
  isExplicit stx || isExplicitApp stx || isLambdaWithImplicit stx || isHole stx || isTacticBlock stx ||
  isNoImplicitLambda stx || isTypeAscription stx

def resolveLocalName (n : Name) : TermElabM (Option (Expr × List String)) := do
  let lctx ← getLCtx
  let auxDeclToFullName := (← read).auxDeclToFullName
  let currNamespace ← getCurrNamespace
  let view := extractMacroScopes n
  /- Simple case. "Match" function for regular local declarations. -/
  let matchLocalDecl? (localDecl : LocalDecl) (givenName : Name) : Option LocalDecl := do
    guard (localDecl.userName == givenName)
    return localDecl
  /-
  "Match" function for auxiliary declarations that correspond to recursive definitions being defined.
  This function is used in the first-pass.
  Note that we do not check for `localDecl.userName == givenName` in this pass as we do for regular local declarations.
  Reason: consider the following example
  ```
    mutual
      inductive Foo
      | somefoo : Foo | bar : Bar → Foo → Foo
      inductive Bar
      | somebar : Bar| foobar : Foo → Bar → Bar
    end

    mutual
      private def Foo.toString : Foo → String
        | Foo.somefoo => go 2 ++ toString.go 2 ++ Foo.toString.go 2
        | Foo.bar b f => toString f ++ Bar.toString b
      where
        go (x : Nat) := s!"foo {x}"

      private def _root_.Ex2.Bar.toString : Bar → String
        | Bar.somebar => "bar"
        | Bar.foobar f b => Foo.toString f ++ Bar.toString b
    end
  ```
  In the example above, we have two local declarations named `toString` in the local context, and
  we want the `toString f` to be resolved to `Foo.toString f`.
  -/
  let matchAuxRecDecl? (localDecl : LocalDecl) (fullDeclName : Name) (givenNameView : MacroScopesView) : Option LocalDecl := do
    let fullDeclView := extractMacroScopes fullDeclName
    /- First cleanup private name annotations -/
    let fullDeclView := { fullDeclView with name := (privateToUserName? fullDeclView.name).getD fullDeclView.name }
    let fullDeclName := fullDeclView.review
    let localDeclNameView := extractMacroScopes localDecl.userName
    /- If the current namespace is a prefix of the full declaration name,
       we use a relaxed matching test where we must satisfy the following conditions
       - The local declaration is a suffix of the given name.
       - The given name is a suffix of the full declaration.

       Recall the `let rec`/`where` declaration naming convention. For example, suppose we have
       ```
       def Foo.Bla.f ... :=
         ... go ...
       where
          go ... := ...
       ```
       The current namespace is `Foo.Bla`, and the full name for `go` is `Foo.Bla.f.g`, but we want to
       refer to it using just `go`. It is also accepted to refer to it using `f.go`, `Bla.f.go`, etc.

    -/
    if currNamespace.isPrefixOf fullDeclName then
      /- Relaxed mode that allows us to access `let rec` declarations using shorter names -/
      guard (localDeclNameView.isSuffixOf givenNameView)
      guard (givenNameView.isSuffixOf fullDeclView)
      return localDecl
    else
      /-
         It is the standard algorithm we are using at `resolveGlobalName` for processing namespaces.

         The current solution also has a limitation when using `def _root_` in a mutual block.
         The non `def _root_` declarations may update the namespace. See the following example:
         ```
         mutual
           def Foo.f ... := ...
           def _root_.g ... := ...
             let rec h := ...
             ...
         end
         ```
         `def Foo.f` updates the namespace. Then, even when processing `def _root_.g ...`
         the condition `currNamespace.isPrefixOf fullDeclName` does not hold.
         This is not a big problem because we are planning to modify how we handle the mutual block in the future.

         Note that we don't check for `localDecl.userName == givenName` here.
      -/
      let rec go (ns : Name) : Option LocalDecl := do
        if { givenNameView with name := ns ++ givenNameView.name }.review == fullDeclName then
          return localDecl
        match ns with
        | .str pre .. => go pre
        | _ => failure
      return (← go currNamespace)
  /- Traverse the local context backwards looking for match `givenNameView`.
     If `skipAuxDecl` we ignore `auxDecl` local declarations. -/
  let findLocalDecl? (givenNameView : MacroScopesView) (skipAuxDecl : Bool) : Option LocalDecl :=
    let givenName := givenNameView.review
    let localDecl? := lctx.decls.findSomeRev? fun localDecl? => do
      let localDecl ← localDecl?
      if localDecl.isAuxDecl then
        guard (!skipAuxDecl)
        if let some fullDeclName := auxDeclToFullName.find? localDecl.fvarId then
          matchAuxRecDecl? localDecl fullDeclName givenNameView
        else
          matchLocalDecl? localDecl givenName
      else
        matchLocalDecl? localDecl givenName
    if localDecl?.isSome || skipAuxDecl then
      localDecl?
    else
      -- Search auxDecls again trying an exact match of the given name
      lctx.decls.findSomeRev? fun localDecl? => do
        let localDecl ← localDecl?
        guard localDecl.isAuxDecl
        matchLocalDecl? localDecl givenName
  /-
  We use the parameter `globalDeclFound` to decide whether we should skip auxiliary declarations or not.
  We set it to true if we found a global declaration `n` as we iterate over the `loop`.
  Without this workaround, we would not be able to elaborate an example such as
  ```
  def foo.aux := 1
  def foo : Nat → Nat
    | n => foo.aux -- should not be interpreted as `(foo).aux`
  ```
  See test `aStructPerfIssue.lean` for another example.
  We skip auxiliary declarations when `projs` is not empty and `globalDeclFound` is true.
  Remark: we did not use to have the `globalDeclFound` parameter. Without this extra check we failed
  to elaborate
  ```
  example : Nat :=
    let n := 0
    n.succ + (m |>.succ) + m.succ
  where
    m := 1
  ```
  See issue #1850.
  -/
  let rec loop (n : Name) (projs : List String) (globalDeclFound : Bool) := do
    let givenNameView := { view with name := n }
    let mut globalDeclFoundNext := globalDeclFound
    unless globalDeclFound do
      let r ← resolveGlobalName givenNameView.review
      let r := r.filter fun (_, fieldList) => fieldList.isEmpty
      unless r.isEmpty do
        globalDeclFoundNext := true
    /-
    Note that we use `globalDeclFound` instead of `globalDeclFoundNext` in the following test.
    Reason: a local should shadow a global with the same name.
    Consider the following example. See issue #3079
    ```
    def foo : Nat := 1

    def bar : Nat :=
      foo.add 1 -- should be 11
    where
      foo := 10
    ```
    -/
    match findLocalDecl? givenNameView (skipAuxDecl := globalDeclFound && !projs.isEmpty) with
    | some decl => return some (decl.toExpr, projs)
    | none => match n with
      | .str pre s => loop pre (s::projs) globalDeclFoundNext
      | _ => return none
  loop view.name [] (globalDeclFound := false)

/-- Return true iff `stx` is a `Syntax.ident`, and it is a local variable. -/
def isLocalIdent? (stx : Syntax) : TermElabM (Option Expr) :=
  match stx with
  | Syntax.ident _ _ val _ => do
    let r? ← resolveLocalName val
    match r? with
    | some (fvar, []) => return some fvar
    | _               => return none
  | _ => return none

inductive UseImplicitLambdaResult where
  | no
  | yes (expectedType : Expr)
  | postpone

/--
  Return normalized expected type if it is of the form `{a : α} → β` or `[a : α] → β` and
  `blockImplicitLambda stx` is not true, else return `none`.

  Remark: implicit lambdas are not triggered by the strict implicit binder annotation `{{a : α}} → β`
-/
private def useImplicitLambda (stx : Syntax) (expectedType? : Option Expr) : TermElabM UseImplicitLambdaResult := do
  if blockImplicitLambda stx then
    return .no
  let some expectedType := expectedType? | return .no
  if hasNoImplicitLambdaAnnotation expectedType then
    return .no
  let expectedType ← whnfForall expectedType
  let .forallE _ _ _ c := expectedType | return .no
  unless c.isImplicit || c.isInstImplicit do
    return .no
  if let some x ← isLocalIdent? stx then
    if (← isMVarApp (← inferType x)) then
      /-
      If `stx` is a local variable without type information, then adding implicit lambdas makes elaboration fail.
      We should try to postpone elaboration until the type of the local variable becomes available, or disable
      implicit lambdas if we cannot postpone anymore.
      Here is an example where this special case is useful.
      ```
      def foo2mk (_ : ∀ {α : Type} (a : α), a = a) : nat := 37
      example (x) : foo2mk x = foo2mk x := rfl
      ```
      The example about would fail without this special case.
      The expected type would be `(a : α✝) → a = a`, where `α✝` is a new free variable introduced by the implicit lambda.
      Now, let `?m` be the type of `x`. Then, the constraint `?m =?= (a : α✝) → a = a` cannot be solved using the
      assignment `?m := (a : α✝) → a = a` since `α✝` is not in the scope of `?m`.

      Note that, this workaround does not prevent the following example from failing.
      ```
      example (x) : foo2mk (id x) = 37 := rfl
      ```
      The user can write
      ```
      example (x) : foo2mk (id @x) = 37 := rfl
      ```
      -/
      return .postpone
  return .yes expectedType

private def decorateErrorMessageWithLambdaImplicitVars (ex : Exception) (impFVars : Array Expr) : TermElabM Exception := do
  match ex with
  | .error ref msg =>
    if impFVars.isEmpty then
      return Exception.error ref msg
    else
      let mut msg := m!"{msg}\nthe following variables have been introduced by the implicit lambda feature"
      for impFVar in impFVars do
        let auxMsg := m!"{impFVar} : {← inferType impFVar}"
        let auxMsg ← addMessageContext auxMsg
        msg := m!"{msg}{indentD auxMsg}"
      msg := m!"{msg}\nyou can disable implicit lambdas using `@` or writing a lambda expression with `\{}` or `[]` binder annotations."
      return Exception.error ref msg
  | _ => return ex

private def elabImplicitLambdaAux (stx : Syntax) (catchExPostpone : Bool) (expectedType : Expr) (impFVars : Array Expr) : TermElabM Expr := do
  let body ← elabUsingElabFns stx expectedType catchExPostpone
  try
    let body ← ensureHasType expectedType body
    let r ← mkLambdaFVars impFVars body
    trace[Elab.implicitForall] r
    return r
  catch ex =>
    throw (← decorateErrorMessageWithLambdaImplicitVars ex impFVars)

private partial def elabImplicitLambda (stx : Syntax) (catchExPostpone : Bool) (type : Expr) : TermElabM Expr :=
  loop type #[]
where
  loop (type : Expr) (fvars : Array Expr) : TermElabM Expr := do
    match (← whnfForall type) with
    | .forallE n d b c =>
      if c.isExplicit then
        elabImplicitLambdaAux stx catchExPostpone type fvars
      else withFreshMacroScope do
        let n ← MonadQuotation.addMacroScope n
        withLocalDecl n c d fun fvar => do
          let type := b.instantiate1 fvar
          loop type (fvars.push fvar)
    | _ =>
      elabImplicitLambdaAux stx catchExPostpone type fvars

/-- Main loop for `elabTerm` -/
private partial def elabTermAux (expectedType? : Option Expr) (catchExPostpone : Bool) (implicitLambda : Bool) : Syntax → TermElabM Expr
  | .missing => mkSyntheticSorryFor expectedType?
  | stx => withFreshMacroScope <| withIncRecDepth do
    withTraceNode `Elab.step (fun _ => return m!"expected type: {expectedType?}, term\n{stx}")
      (tag := stx.getKind.toString) do
    checkSystem "elaborator"
    let env ← getEnv
    let result ← match (← liftMacroM (expandMacroImpl? env stx)) with
    | some (decl, stxNew?) =>
      let stxNew ← liftMacroM <| liftExcept stxNew?
      withInfoContext' stx (mkInfo := mkTermInfo decl (expectedType? := expectedType?) stx) <|
        withMacroExpansion stx stxNew <|
          withRef stxNew <|
            elabTermAux expectedType? catchExPostpone implicitLambda stxNew
    | _ =>
      let useImplicitResult ← if implicitLambda && (← read).implicitLambda then useImplicitLambda stx expectedType? else pure .no
      match useImplicitResult with
      | .yes expectedType => elabImplicitLambda stx catchExPostpone expectedType
      | .no => elabUsingElabFns stx expectedType? catchExPostpone
      | .postpone =>
        /-
        Try to postpone elaboration, and if we cannot postpone anymore disable implicit lambdas.
        See comment at `useImplicitLambda`.
        -/
        if (← read).mayPostpone then
          if catchExPostpone then
            postponeElabTerm stx expectedType?
          else
            throwPostpone
        else
          elabUsingElabFns stx expectedType? catchExPostpone
    trace[Elab.step.result] result
    pure result

/-- Store in the `InfoTree` that `e` is a "dot"-completion target. `stx` should cover the entire term. -/
def addDotCompletionInfo (stx : Syntax) (e : Expr) (expectedType? : Option Expr) : TermElabM Unit := do
  addCompletionInfo <| CompletionInfo.dot { expr := e, stx, lctx := (← getLCtx), elaborator := .anonymous, expectedType? } (expectedType? := expectedType?)

/--
  Main function for elaborating terms.
  It extracts the elaboration methods from the environment using the node kind.
  Recall that the environment has a mapping from `SyntaxNodeKind` to `TermElab` methods.
  It creates a fresh macro scope for executing the elaboration method.
  All unlogged trace messages produced by the elaboration method are logged using
  the position information at `stx`. If the elaboration method throws an `Exception.error` and `errToSorry == true`,
  the error is logged and a synthetic sorry expression is returned.
  If the elaboration throws `Exception.postpone` and `catchExPostpone == true`,
  a new synthetic metavariable of kind `SyntheticMVarKind.postponed` is created, registered,
  and returned.
  The option `catchExPostpone == false` is used to implement `resumeElabTerm`
  to prevent the creation of another synthetic metavariable when resuming the elaboration.

  If `implicitLambda == false`, then disable implicit lambdas feature for the given syntax, but not for its subterms.
  We use this flag to implement, for example, the `@` modifier. If `Context.implicitLambda == false`, then this parameter has no effect.
  -/
def elabTerm (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone := true) (implicitLambda := true) : TermElabM Expr :=
  withRef stx <| elabTermAux expectedType? catchExPostpone implicitLambda stx

/--
Similar to `Lean.Elab.Term.elabTerm`, but ensures that the type of the elaborated term is `expectedType?`
by inserting coercions if necessary.

If `errToSorry` is true, then if coercion insertion fails, this function returns `sorry` and logs the error.
Otherwise, it throws the error.
-/
def elabTermEnsuringType (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone := true) (implicitLambda := true) (errorMsgHeader? : Option String := none) : TermElabM Expr := do
  let e ← elabTerm stx expectedType? catchExPostpone implicitLambda
  try
    withRef stx <| ensureHasType expectedType? e errorMsgHeader?
  catch ex =>
    if (← read).errToSorry && ex matches .error .. then
      exceptionToSorry ex expectedType?
    else
      throw ex

/-- Execute `x` and return `some` if no new errors were recorded or exceptions were thrown. Otherwise, return `none`. -/
def commitIfNoErrors? (x : TermElabM α) : TermElabM (Option α) := do
  let saved ← saveState
  Core.resetMessageLog
  try
    let a ← x
    if (← MonadLog.hasErrors) then
      restoreState saved
      return none
    else
      Core.setMessageLog (saved.meta.core.messages ++ (← Core.getMessageLog))
      return a
  catch _ =>
    restoreState saved
    return none

/-- Adapt a syntax transformation to a regular, term-producing elaborator. -/
def adaptExpander (exp : Syntax → TermElabM Syntax) : TermElab := fun stx expectedType? => do
  let stx' ← exp stx
  withMacroExpansion stx stx' <| elabTerm stx' expectedType?

/--
  Create a new metavariable with the given type, and try to synthesize it.
  If type class resolution cannot be executed (e.g., it is stuck because of metavariables in `type`),
  register metavariable as a pending one.
-/
def mkInstMVar (type : Expr) (extraErrorMsg? : Option MessageData := none) : TermElabM Expr := do
  let mvar ← mkFreshExprMVar type MetavarKind.synthetic
  let mvarId := mvar.mvarId!
  unless (← synthesizeInstMVarCore mvarId (extraErrorMsg? := extraErrorMsg?)) do
    registerSyntheticMVarWithCurrRef mvarId (.typeClass extraErrorMsg?)
  return mvar

/--
  Make sure `e` is a type by inferring its type and making sure it is an `Expr.sort`
  or is unifiable with `Expr.sort`, or can be coerced into one. -/
def ensureType (e : Expr) : TermElabM Expr := do
  if (← isType e) then
    return e
  else
    let eType ← inferType e
    let u ← mkFreshLevelMVar
    if (← isDefEq eType (mkSort u)) then
      return e
    else if let some coerced ← coerceToSort? e then
      return coerced
    else
      if (← instantiateMVars e).hasSyntheticSorry then
        throwAbortTerm
      throwError "type expected, got\n  ({← instantiateMVars e} : {← instantiateMVars eType})"

/-- Elaborate `stx` and ensure result is a type. -/
def elabType (stx : Syntax) : TermElabM Expr := do
  let u ← mkFreshLevelMVar
  let type ← elabTerm stx (mkSort u)
  withRef stx <| ensureType type

/--
  Enable auto-bound implicits, and execute `k` while catching auto bound implicit exceptions. When an exception is caught,
  a new local declaration is created, registered, and `k` is tried to be executed again. -/
partial def withAutoBoundImplicit (k : TermElabM α) : TermElabM α := do
  let flag := autoImplicit.get (← getOptions)
  if flag then
    withReader (fun ctx => { ctx with autoBoundImplicit := flag, autoBoundImplicits := {} }) do
      let rec loop (s : SavedState) : TermElabM α := withIncRecDepth do
        checkSystem "auto-implicit"
        try
          k
        catch
          | ex => match isAutoBoundImplicitLocalException? ex with
            | some n =>
              -- Restore state, declare `n`, and try again
              s.restore (restoreInfo := true)
              withLocalDecl n .implicit (← mkFreshTypeMVar) fun x =>
                withReader (fun ctx => { ctx with autoBoundImplicits := ctx.autoBoundImplicits.push x } ) do
                  loop (← saveState)
            | none   => throw ex
      loop (← saveState)
  else
    k

def withoutAutoBoundImplicit (k : TermElabM α) : TermElabM α := do
  withReader (fun ctx => { ctx with autoBoundImplicit := false, autoBoundImplicits := {} }) k

partial def withAutoBoundImplicitForbiddenPred (p : Name → Bool) (x : TermElabM α) : TermElabM α := do
  withReader (fun ctx => { ctx with autoBoundImplicitForbidden := fun n => p n || ctx.autoBoundImplicitForbidden n }) x

/--
  Collect unassigned metavariables in `type` that are not already in `init` and not satisfying `except`.
-/
partial def collectUnassignedMVars (type : Expr) (init : Array Expr := #[]) (except : MVarId → Bool := fun _ => false)
    : TermElabM (Array Expr) := do
  let mvarIds ← getMVars type
  if mvarIds.isEmpty then
    return init
  else
    go mvarIds.toList init init
where
  go (mvarIds : List MVarId) (result visited : Array Expr) : TermElabM (Array Expr) := do
    match mvarIds with
    | [] => return result
    | mvarId :: mvarIds => do
      let visited := visited.push (mkMVar mvarId)
      if (← mvarId.isAssigned) then
        go mvarIds result visited
      else if result.contains (mkMVar mvarId) || except mvarId then
        go mvarIds result visited
      else
        let mvarType := (← getMVarDecl mvarId).type
        let mvarIdsNew ← getMVars mvarType
        let mvarIdsNew := mvarIdsNew.filter fun mvarId => !visited.contains (mkMVar mvarId)
        if mvarIdsNew.isEmpty then
          go mvarIds (result.push (mkMVar mvarId)) visited
        else
          go (mvarIdsNew.toList ++ mvarId :: mvarIds) result visited

/--
  Return `autoBoundImplicits ++ xs`
  This method throws an error if a variable in `autoBoundImplicits` depends on some `x` in `xs`.
  The `autoBoundImplicits` may contain free variables created by the auto-implicit feature, and unassigned free variables.
  It avoids the hack used at `autoBoundImplicitsOld`.

  Remark: we cannot simply replace every occurrence of `addAutoBoundImplicitsOld` with this one because a particular
  use-case may not be able to handle the metavariables in the array being given to `k`.
-/
def addAutoBoundImplicits (xs : Array Expr) : TermElabM (Array Expr) := do
  let autos := (← read).autoBoundImplicits
  go autos.toList #[]
where
  go (todo : List Expr) (autos : Array Expr) : TermElabM (Array Expr) := do
    match todo with
    | [] =>
      for auto in autos do
        if auto.isFVar then
          let localDecl ← auto.fvarId!.getDecl
          for x in xs do
            if (← localDeclDependsOn localDecl x.fvarId!) then
              throwError "invalid auto implicit argument '{auto}', it depends on explicitly provided argument '{x}'"
      return autos ++ xs
    | auto :: todo =>
      let autos ← collectUnassignedMVars (← inferType auto) autos
      go todo (autos.push auto)

/--
  Similar to `autoBoundImplicits`, but immediately if the resulting array of expressions contains metavariables,
  it immediately uses `mkForallFVars` + `forallBoundedTelescope` to convert them into free variables.
  The type `type` is modified during the process if type depends on `xs`.
  We use this method to simplify the conversion of code using `autoBoundImplicitsOld` to `autoBoundImplicits`.
-/
def addAutoBoundImplicits' (xs : Array Expr) (type : Expr) (k : Array Expr → Expr → TermElabM α) : TermElabM α := do
  let xs ← addAutoBoundImplicits xs
  if xs.all (·.isFVar) then
    k xs type
  else
    forallBoundedTelescope (← mkForallFVars xs type) xs.size fun xs type => k xs type

def mkAuxName (suffix : Name) : TermElabM Name := do
  match (← read).declName? with
  | none          => throwError "auxiliary declaration cannot be created when declaration name is not available"
  | some declName => Lean.mkAuxName (declName ++ suffix) 1

builtin_initialize registerTraceClass `Elab.letrec

/-- Return true if mvarId is an auxiliary metavariable created for compiling `let rec` or it
   is delayed assigned to one. -/
def isLetRecAuxMVar (mvarId : MVarId) : TermElabM Bool := do
  trace[Elab.letrec] "mvarId: {mkMVar mvarId} letrecMVars: {(← get).letRecsToLift.map (mkMVar $ ·.mvarId)}"
  let mvarId ← getDelayedMVarRoot mvarId
  trace[Elab.letrec] "mvarId root: {mkMVar mvarId}"
  return (← get).letRecsToLift.any (·.mvarId == mvarId)

/--
  Create an `Expr.const` using the given name and explicit levels.
  Remark: fresh universe metavariables are created if the constant has more universe
  parameters than `explicitLevels`.

  If `checkDeprecated := true`, then `Linter.checkDeprecated` is invoked.
-/
def mkConst (constName : Name) (explicitLevels : List Level := []) (checkDeprecated := true) : TermElabM Expr := do
  if checkDeprecated then
    Linter.checkDeprecated constName
  let cinfo ← getConstInfo constName
  if explicitLevels.length > cinfo.levelParams.length then
    throwError "too many explicit universe levels for '{constName}'"
  else
    let numMissingLevels := cinfo.levelParams.length - explicitLevels.length
    let us ← mkFreshLevelMVars numMissingLevels
    return Lean.mkConst constName (explicitLevels ++ us)

def checkDeprecated (ref : Syntax) (e : Expr) : TermElabM Unit := do
  if let .const declName _ := e.getAppFn then
    withRef ref do Linter.checkDeprecated declName

private def mkConsts (candidates : List (Name × List String)) (explicitLevels : List Level) : TermElabM (List (Expr × List String)) := do
  candidates.foldlM (init := []) fun result (declName, projs) => do
    -- TODO: better support for `mkConst` failure. We may want to cache the failures, and report them if all candidates fail.
    /-
    We disable `checkDeprecated` here because there may be many overloaded symbols.
    Note that, this method and `resolveName` and `resolveName'` return a list of pairs instead of a list of `TermElabResult`s.
    We perform the `checkDeprecated` test at `resolveId?` and `elabAppFnId`.
    At `elabAppFnId`, we perform the check when converting the list returned by `resolveName'` into a list of
    `TermElabResult`s.
    -/
    let const ← mkConst declName explicitLevels (checkDeprecated := false)
    return (const, projs) :: result

def resolveName (stx : Syntax) (n : Name) (preresolved : List Syntax.Preresolved) (explicitLevels : List Level) (expectedType? : Option Expr := none) : TermElabM (List (Expr × List String)) := do
  addCompletionInfo <| CompletionInfo.id stx stx.getId (danglingDot := false) (← getLCtx) expectedType?
  if let some (e, projs) ← resolveLocalName n then
    unless explicitLevels.isEmpty do
      throwError "invalid use of explicit universe parameters, '{e}' is a local"
    return [(e, projs)]
  let preresolved := preresolved.filterMap fun
    | .decl n projs => some (n, projs)
    | _             => none
  -- check for section variable capture by a quotation
  let ctx ← read
  if let some (e, projs) := preresolved.findSome? fun (n, projs) => ctx.sectionFVars.find? n |>.map (·, projs) then
    return [(e, projs)]  -- section variables should shadow global decls
  if preresolved.isEmpty then
    process (← realizeGlobalName n)
  else
    process preresolved
where
  process (candidates : List (Name × List String)) : TermElabM (List (Expr × List String)) := do
    if candidates.isEmpty then
      if (← read).autoBoundImplicit &&
           !(← read).autoBoundImplicitForbidden n &&
           isValidAutoBoundImplicitName n (relaxedAutoImplicit.get (← getOptions)) then
        throwAutoBoundImplicitLocal n
      else
        throwError "unknown identifier '{Lean.mkConst n}'"
    mkConsts candidates explicitLevels

/--
  Similar to `resolveName`, but creates identifiers for the main part and each projection with position information derived from `ident`.
  Example: Assume resolveName `v.head.bla.boo` produces `(v.head, ["bla", "boo"])`, then this method produces
  `(v.head, id, [f₁, f₂])` where `id` is an identifier for `v.head`, and `f₁` and `f₂` are identifiers for fields `"bla"` and `"boo"`. -/
def resolveName' (ident : Syntax) (explicitLevels : List Level) (expectedType? : Option Expr := none) : TermElabM (List (Expr × Syntax × List Syntax)) := do
  match ident with
  | .ident _ _ n preresolved =>
    let r ← resolveName ident n preresolved explicitLevels expectedType?
    r.mapM fun (c, fields) => do
      let ids := ident.identComponents (nFields? := fields.length)
      return (c, ids.head!, ids.tail!)
  | _ => throwError "identifier expected"

def resolveId? (stx : Syntax) (kind := "term") (withInfo := false) : TermElabM (Option Expr) := withRef stx do
  match stx with
  | .ident _ _ val preresolved =>
    let rs ← try resolveName stx val preresolved [] catch _ => pure []
    let rs := rs.filter fun ⟨_, projs⟩ => projs.isEmpty
    let fs := rs.map fun (f, _) => f
    match fs with
    | []  => return none
    | [f] =>
      let f ← if withInfo then addTermInfo stx f else pure f
      checkDeprecated stx f
      return some f
    | _   => throwError "ambiguous {kind}, use fully qualified name, possible interpretations {fs}"
  | _ => throwError "identifier expected"

def TermElabM.run (x : TermElabM α) (ctx : Context := {}) (s : State := {}) : MetaM (α × State) :=
  withConfig setElabConfig (x ctx |>.run s)

@[inline] def TermElabM.run' (x : TermElabM α) (ctx : Context := {}) (s : State := {}) : MetaM α :=
  (·.1) <$> x.run ctx s

def TermElabM.toIO (x : TermElabM α)
    (ctxCore : Core.Context) (sCore : Core.State)
    (ctxMeta : Meta.Context) (sMeta : Meta.State)
    (ctx : Context) (s : State) : IO (α × Core.State × Meta.State × State) := do
  let ((a, s), sCore, sMeta) ← (x.run ctx s).toIO ctxCore sCore ctxMeta sMeta
  return (a, sCore, sMeta, s)

/--
  Execute `x` and then tries to solve pending universe constraints.
  Note that, stuck constraints will not be discarded.
-/
def universeConstraintsCheckpoint (x : TermElabM α) : TermElabM α := do
  let a ← x
  discard <| processPostponed (mayPostpone := true) (exceptionOnFailure := true)
  return a

def expandDeclId (currNamespace : Name) (currLevelNames : List Name) (declId : Syntax) (modifiers : Modifiers) : TermElabM ExpandDeclIdResult := do
  let r ← Elab.expandDeclId currNamespace currLevelNames declId modifiers
  if (← read).sectionVars.contains r.shortName then
    throwError "invalid declaration name '{r.shortName}', there is a section variable with the same name"
  return r

/--
  Helper function for "embedding" an `Expr` in `Syntax`.
  It creates a named hole `?m` and immediately assigns `e` to it.
  Examples:
  ```lean
  let e := mkConst ``Nat.zero
  `(Nat.succ $(← exprToSyntax e))
  ```
-/
def exprToSyntax (e : Expr) : TermElabM Term := withFreshMacroScope do
  let result ← `(?m)
  let eType ← inferType e
  let mvar ← elabTerm result eType
  mvar.mvarId!.assign e
  return result

end Term

open Term in
def withoutModifyingStateWithInfoAndMessages [MonadControlT TermElabM m] [Monad m] (x : m α) : m α := do
  controlAt TermElabM fun runInBase => withoutModifyingStateWithInfoAndMessagesImpl <| runInBase x

builtin_initialize
  registerTraceClass `Elab.postpone
  registerTraceClass `Elab.coe
  registerTraceClass `Elab.debug
  registerTraceClass `Elab.reuse

builtin_initialize incrementalAttr : TagAttribute ←
  registerTagAttribute `incremental "Marks an elaborator (tactic or command, currently) as \
supporting incremental elaboration. For unmarked elaborators, the corresponding snapshot bundle \
field in the elaboration context is unset so as to prevent accidental, incorrect reuse."

builtin_initialize builtinIncrementalElabs : IO.Ref NameSet ← IO.mkRef {}

def addBuiltinIncrementalElab (decl : Name) : IO Unit := do
  builtinIncrementalElabs.modify fun s => s.insert decl

builtin_initialize
  registerBuiltinAttribute {
    name            := `builtin_incremental
    descr           := s!"(builtin) {incrementalAttr.attr.descr}"
    applicationTime := .afterCompilation
    add             := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'builtin_incremental', must be global"
      declareBuiltin decl <| mkApp (mkConst ``addBuiltinIncrementalElab) (toExpr decl)
  }

/-- Checks whether a declaration is annotated with `[builtin_incremental]` or `[incremental]`. -/
def isIncrementalElab [Monad m] [MonadEnv m] [MonadLiftT IO m] (decl : Name) : m Bool :=
  (return (← builtinIncrementalElabs.get (m := IO)).contains decl) <||>
  (return incrementalAttr.hasTag (← getEnv) decl)

export Term (TermElabM)

builtin_initialize
  registerTraceClass `Elab.implicitForall

end Lean.Elab
