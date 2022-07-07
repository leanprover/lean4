/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.ResolveName
import Lean.Log
import Lean.Util.Sorry
import Lean.Util.ReplaceExpr
import Lean.Structure
import Lean.Meta.AppBuilder
import Lean.Meta.CollectMVars
import Lean.Meta.Coe
import Lean.Hygiene
import Lean.Util.RecDepth

import Lean.Elab.Config
import Lean.Elab.Level
import Lean.Elab.Attributes
import Lean.Elab.AutoBound
import Lean.Elab.InfoTree
import Lean.Elab.Open
import Lean.Elab.SetOption
import Lean.Elab.DeclModifiers

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

/-- We use synthetic metavariables as placeholders for pending elaboration steps. -/
inductive SyntheticMVarKind where
  | /-- Use typeclass resolution to synthesize value for metavariable. -/
    typeClass
  | /--
     Similar to `typeClass`, but error messages are different.
     if `f?` is `some f`, we produce an application type mismatch error message.
     Otherwise, if `header?` is `some header`, we generate the error `(header ++ "has type" ++ eType ++ "but it is expected to have type" ++ expectedType)`
     Otherwise, we generate the error `("type mismatch" ++ e ++ "has type" ++ eType ++ "but it is expected to have type" ++ expectedType)` -/
    coe (header? : Option String) (eNew : Expr) (expectedType : Expr) (eType : Expr) (e : Expr) (f? : Option Expr)
  | /-- Use tactic to synthesize value for metavariable. -/
    tactic (tacticCode : Syntax) (ctx : SavedContext)
  | /-- Metavariable represents a hole whose elaboration has been postponed. -/
    postponed (ctx : SavedContext)

instance : ToString SyntheticMVarKind where
  toString
    | SyntheticMVarKind.typeClass    => "typeclass"
    | SyntheticMVarKind.coe ..       => "coe"
    | SyntheticMVarKind.tactic ..    => "tactic"
    | SyntheticMVarKind.postponed .. => "postponed"

structure SyntheticMVarDecl where
  mvarId : MVarId
  stx : Syntax
  kind : SyntheticMVarKind

/--
  We can optionally associate an error context with a metavariable (see `MVarErrorInfo`).
  We have three different kinds of error context.
-/
inductive MVarErrorKind where
  | /-- Metavariable for implicit arguments. `ctx` is the parent application. -/
    implicitArg (ctx : Expr)
  | /-- Metavariable for explicit holes provided by the user (e.g., `_` and `?m`) -/
    hole
  | /-- "Custom", `msgData` stores the additional error messages. -/
    custom (msgData : MessageData)
  deriving Inhabited

instance : ToString MVarErrorKind where
  toString
    | MVarErrorKind.implicitArg _   => "implicitArg"
    | MVarErrorKind.hole            => "hole"
    | MVarErrorKind.custom _        => "custom"

/--
  We can optionally associate an error context with metavariables.
-/
structure MVarErrorInfo where
  mvarId    : MVarId
  ref       : Syntax
  kind      : MVarErrorKind
  argName?  : Option Name := none
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
  deriving Inhabited

/--
  State of the `TermElabM` monad.
-/
structure State where
  levelNames        : List Name       := []
  syntheticMVars    : List SyntheticMVarDecl := []
  mvarErrorInfos    : MVarIdMap MVarErrorInfo := {}
  letRecsToLift     : List LetRecToLift := []
  infoState         : InfoState := {}
  deriving Inhabited

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
  deriving Inhabited

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
   pre  : Std.PHashMap CacheKey Snapshot := {}
   post : Std.PHashMap CacheKey Snapshot := {}
   deriving Inhabited

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
  autoBoundImplicits : Std.PArray Expr := {}
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
  /-- Noncomputable sections automatically add the `noncomputable` modifier to any declaration we cannot generate code for  -/
  isNoncomputableSection : Bool        := false
  /-- When `true` we skip TC failures. We use this option when processing patterns -/
  ignoreTCFailures : Bool := false
  /-- `true` when elaborating patterns. It affects how we elaborate named holes. -/
  inPattern        : Bool := false
  /-- Cache for the `save` tactic. It is only `some` in the LSP server. -/
  tacticCache?     : Option (IO.Ref Tactic.Cache) := none
  /-- If `true`, we store in the `Expr` the `Syntax` for recursive applications (i.e., applications
      of free variables tagged with `isAuxDecl`). We store the `Syntax` using `mkRecAppWithSyntax`.
      We use the `Syntax` object to produce better error messages at `Structural.lean` and `WF.lean`. -/
  saveRecAppSyntax : Bool := true

abbrev TermElabM := ReaderT Context $ StateRefT State MetaM
abbrev TermElab  := Syntax → Option Expr → TermElabM Expr

-- Make the compiler generate specialized `pure`/`bind` so we do not have to optimize through the
-- whole monad stack at every use site. May eventually be covered by `deriving`.
instance : Monad TermElabM := let i := inferInstanceAs (Monad TermElabM); { pure := i.pure, bind := i.bind }

open Meta

instance : Inhabited (TermElabM α) where
  default := throw default

/--
  Backtrackable state for the `TermElabM` monad.
-/
structure SavedState where
  meta   : Meta.SavedState
  «elab» : State
  deriving Inhabited

protected def saveState : TermElabM SavedState :=
  return { meta := (← Meta.saveState), «elab» := (← get) }

def SavedState.restore (s : SavedState) (restoreInfo : Bool := false) : TermElabM Unit := do
  let traceState ← getTraceState -- We never backtrack trace message
  let infoState := (← get).infoState -- We also do not backtrack the info nodes when `restoreInfo == false`
  s.meta.restore
  set s.elab
  setTraceState traceState
  unless restoreInfo do
    modify fun s => { s with infoState := infoState }

instance : MonadBacktrack SavedState TermElabM where
  saveState      := Term.saveState
  restoreState b := b.restore

abbrev TermElabResult (α : Type) := EStateM.Result Exception SavedState α

instance [Inhabited α] : Inhabited (TermElabResult α) where
  default := EStateM.Result.ok default default

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
    | ex@(Exception.error _ _) =>
      let sNew ← saveState
      s.restore (restoreInfo := true)
      return EStateM.Result.error ex sNew
    | ex@(Exception.internal id _) =>
      if id == postponeExceptionId then
        s.restore (restoreInfo := true)
      throw ex

/--
  Apply the result/exception and state captured with `observing`.
  We use this method to implement overloaded notation and symbols. -/
def applyResult (result : TermElabResult α) : TermElabM α := do
  match result with
  | EStateM.Result.ok a r     => r.restore (restoreInfo := true); return a
  | EStateM.Result.error ex r => r.restore (restoreInfo := true); throw ex

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

instance : MonadInfoTree TermElabM where
  getInfoState      := return (← get).infoState
  modifyInfoState f := modify fun s => { s with infoState := f s.infoState }

/--
  Execute `x` but discard changes performed at `Term.State` and `Meta.State`.
  Recall that the environment is at `Core.State`. Thus, any updates to it will
  be preserved. This method is useful for performing computations where all
  metavariable must be resolved or discarded.
  The info trees are not discarded, however, and wrapped in `InfoTree.Context`
  to store their metavariable context. -/
def withoutModifyingElabMetaStateWithInfo (x : TermElabM α) : TermElabM α := do
  let s ← get
  let sMeta ← getThe Meta.State
  try
     withSaveInfoContext x
  finally
    modify ({ s with infoState := ·.infoState })
    set sMeta

/--
  Execute `x` bud discard changes performed to the state.
  However, the info trees and messages are not discarded. -/
private def withoutModifyingStateWithInfoAndMessagesImpl (x : TermElabM α) : TermElabM α := do
  let saved ← saveState
  try
    withSaveInfoContext x
  finally
    let saved := { saved with elab.infoState := (← get).infoState, meta.core.messages := (← getThe Core.State).messages }
    restoreState saved

/--
  Execute `x` without storing `Syntax` for recursive applications. See `saveRecAppSyntax` field at `Context`.
-/
def withoutSavingRecAppSyntax (x : TermElabM α) : TermElabM α :=
  withReader (fun ctx => { ctx with saveRecAppSyntax := false }) x

unsafe def mkTermElabAttributeUnsafe : IO (KeyedDeclsAttribute TermElab) :=
  mkElabAttribute TermElab `Lean.Elab.Term.termElabAttribute `builtinTermElab `termElab `Lean.Parser.Term `Lean.Elab.Term.TermElab "term"

@[implementedBy mkTermElabAttributeUnsafe]
opaque mkTermElabAttribute : IO (KeyedDeclsAttribute TermElab)

builtin_initialize termElabAttribute : KeyedDeclsAttribute TermElab ← mkTermElabAttribute

inductive GetOpKind where
  | /-- `a[i]` -/  safe
  | /-- `a[i]!` -/ panic
  | /-- `a[i]?` -/ optional

def GetOpKind.opName : GetOpKind → String
  | safe => "getOp"
  | panic => "getOp!"
  | optional => "getOp?"

/--
  Auxiliary datatatype for presenting a Lean lvalue modifier.
  We represent a unelaborated lvalue as a `Syntax` (or `Expr`) and `List LVal`.
  Example: `a.foo[i].1` is represented as the `Syntax` `a` and the list
  `[LVal.fieldName "foo", LVal.getOp i, LVal.fieldIdx 1]`.
  Recall that the notation `a[i]` is not just for accessing arrays in Lean. -/
inductive LVal where
  | fieldIdx  (ref : Syntax) (i : Nat)
    /- Field `suffix?` is for producing better error messages because `x.y` may be a field access or a hierachical/composite name.
       `ref` is the syntax object representing the field. `targetStx` is the target object being accessed. -/
  | fieldName (ref : Syntax) (name : String) (suffix? : Option Name) (targetStx : Syntax)
  | getOp     (ref : Syntax) (idx : Syntax) (getOpKind : GetOpKind)

def LVal.getRef : LVal → Syntax
  | LVal.fieldIdx ref _    => ref
  | LVal.fieldName ref ..  => ref
  | LVal.getOp ref ..      => ref

def LVal.isFieldName : LVal → Bool
  | LVal.fieldName .. => true
  | _ => false

instance : ToString LVal where
  toString
    | LVal.fieldIdx _ i     => toString i
    | LVal.fieldName _ n .. => n
    | LVal.getOp _ idx k    =>
      let r := "[" ++ toString idx ++ "]"
      match k with
      | .safe => r
      | .panic => r ++ "!"
      | .optional => r ++ "?"

/-- Return the name of the declaration being elaborated if available. -/
def getDeclName? : TermElabM (Option Name) := return (← read).declName?
/-- Return the list of nested `let rec` declarations that need to be lifted. -/
def getLetRecsToLift : TermElabM (List LetRecToLift) := return (← get).letRecsToLift
/-- Return the declaration of the given metavariable -/
def getMVarDecl (mvarId : MVarId) : TermElabM MetavarDecl := return (← getMCtx).getDecl mvarId

/-- Execute `x` with `declName? := name`. See `getDeclName? -/
def withDeclName (name : Name) (x : TermElabM α) : TermElabM α :=
  withReader (fun ctx => { ctx with declName? := name }) x

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
  withLocalDecl shortDeclName BinderInfo.auxDecl type fun x =>
    withReader (fun ctx => { ctx with auxDeclToFullName := ctx.auxDeclToFullName.insert x.fvarId! declName }) do
      k x

/--
  Execute `x` without converting errors (i.e., exceptions) to `sorry` applications.
  Recall that when `errToSorry = true`, the method `elabTerm` catches exceptions and convert them into `sorry` applications.
-/
def withoutErrToSorry (x : TermElabM α) : TermElabM α :=
  withReader (fun ctx => { ctx with errToSorry := false }) x

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
  | EStateM.Result.ok a newS  => setMCtx newS.mctx; setNGen newS.ngen; setLevelNames newS.levelNames; pure a
  | EStateM.Result.error ex _ => throw ex

def elabLevel (stx : Syntax) : TermElabM Level :=
  liftLevelM <| Level.elabLevel stx

/- Elaborate `x` with `stx` on the macro stack -/
def withMacroExpansion (beforeStx afterStx : Syntax) (x : TermElabM α) : TermElabM α :=
  withMacroExpansionInfo beforeStx afterStx do
    withReader (fun ctx => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

/-
  Add the given metavariable to the list of pending synthetic metavariables.
  The method `synthesizeSyntheticMVars` is used to process the metavariables on this list. -/
def registerSyntheticMVar (stx : Syntax) (mvarId : MVarId) (kind : SyntheticMVarKind) : TermElabM Unit := do
  modify fun s => { s with syntheticMVars := { mvarId := mvarId, stx := stx, kind := kind } :: s.syntheticMVars }

def registerSyntheticMVarWithCurrRef (mvarId : MVarId) (kind : SyntheticMVarKind) : TermElabM Unit := do
  registerSyntheticMVar (← getRef) mvarId kind

def registerMVarErrorInfo (mvarErrorInfo : MVarErrorInfo) : TermElabM Unit :=
  modify fun s => { s with mvarErrorInfos := s.mvarErrorInfos.insert mvarErrorInfo.mvarId mvarErrorInfo }

def registerMVarErrorHoleInfo (mvarId : MVarId) (ref : Syntax) : TermElabM Unit :=
  registerMVarErrorInfo { mvarId := mvarId, ref := ref, kind := MVarErrorKind.hole }

def registerMVarErrorImplicitArgInfo (mvarId : MVarId) (ref : Syntax) (app : Expr) : TermElabM Unit := do
  registerMVarErrorInfo { mvarId := mvarId, ref := ref, kind := MVarErrorKind.implicitArg app }

def registerMVarErrorCustomInfo (mvarId : MVarId) (ref : Syntax) (msgData : MessageData) : TermElabM Unit := do
  registerMVarErrorInfo { mvarId := mvarId, ref := ref, kind := MVarErrorKind.custom msgData }

def getMVarErrorInfo? (mvarId : MVarId) : TermElabM (Option MVarErrorInfo) := do
  return (← get).mvarErrorInfos.find? mvarId

def registerCustomErrorIfMVar (e : Expr) (ref : Syntax) (msgData : MessageData) : TermElabM Unit :=
  match e.getAppFn with
  | Expr.mvar mvarId _ => registerMVarErrorCustomInfo mvarId ref msgData
  | _ => pure ()

/-
  Auxiliary method for reporting errors of the form "... contains metavariables ...".
  This kind of error is thrown, for example, at `Match.lean` where elaboration
  cannot continue if there are metavariables in patterns.
  We only want to log it if we haven't logged any error so far. -/
def throwMVarError (m : MessageData) : TermElabM α := do
  if (← MonadLog.hasErrors) then
    throwAbortTerm
  else
    throwError m

def MVarErrorInfo.logError (mvarErrorInfo : MVarErrorInfo) (extraMsg? : Option MessageData) : TermElabM Unit := do
  match mvarErrorInfo.kind with
  | MVarErrorKind.implicitArg app => do
    let app ← instantiateMVars app
    let msg := addArgName "don't know how to synthesize implicit argument"
    let msg := msg ++ m!"{indentExpr app.setAppPPExplicitForExposingMVars}" ++ Format.line ++ "context:" ++ Format.line ++ MessageData.ofGoal mvarErrorInfo.mvarId
    logErrorAt mvarErrorInfo.ref (appendExtra msg)
  | MVarErrorKind.hole => do
    let msg := addArgName "don't know how to synthesize placeholder" " for argument"
    let msg := msg ++ Format.line ++ "context:" ++ Format.line ++ MessageData.ofGoal mvarErrorInfo.mvarId
    logErrorAt mvarErrorInfo.ref (MessageData.tagged `Elab.synthPlaceholder <| appendExtra msg)
  | MVarErrorKind.custom msg =>
    logErrorAt mvarErrorInfo.ref (appendExtra msg)
where
  /-- Append `mvarErrorInfo` argument name (if available) to the message.
      Remark: if the argument name contains macro scopes we do not append it. -/
  addArgName (msg : MessageData) (extra : String := "") : MessageData :=
    match mvarErrorInfo.argName? with
    | none => msg
    | some argName => if argName.hasMacroScopes then msg else msg ++ extra ++ m!" '{argName}'"

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
    for (_, mvarErrorInfo) in (← get).mvarErrorInfos do
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
      withMVarContext error.mvarId do
        error.logError extraMsg?
    return hasNewErrors

/-- Ensure metavariables registered using `registerMVarErrorInfos` (and used in the given declaration) have been assigned. -/
def ensureNoUnassignedMVars (decl : Declaration) : TermElabM Unit := do
  let pendingMVarIds ← getMVarsAtDecl decl
  if (← logUnassignedUsingErrorInfos pendingMVarIds) then
    throwAbortCommand

/-
  Execute `x` without allowing it to postpone elaboration tasks.
  That is, `tryPostpone` is a noop. -/
def withoutPostponing (x : TermElabM α) : TermElabM α :=
  withReader (fun ctx => { ctx with mayPostpone := false }) x

/-- Creates syntax for `(` <ident> `:` <type> `)` -/
def mkExplicitBinder (ident : Syntax) (type : Syntax) : Syntax :=
  mkNode ``Lean.Parser.Term.explicitBinder #[mkAtom "(", mkNullNode #[ident], mkNullNode #[mkAtom ":", type], mkNullNode, mkAtom ")"]

/--
  Convert unassigned universe level metavariables into parameters.
  The new parameter names are of the form `u_i` where `i >= nextParamIdx`.
  The method returns the updated expression and new `nextParamIdx`.

  Remark: we make sure the generated parameter names do not clash with the universe at `ctx.levelNames`. -/
def levelMVarToParam (e : Expr) (nextParamIdx : Nat := 1) (except : MVarId → Bool := fun _ => false) : TermElabM (Expr × Nat) := do
  let levelNames ← getLevelNames
  let r := (← getMCtx).levelMVarToParam (fun n => levelNames.elem n) except e `u nextParamIdx
  setMCtx r.mctx
  return (r.expr, r.nextParamIdx)

/-- Variant of `levelMVarToParam` where `nextParamIdx` is stored in a state monad. -/
def levelMVarToParam' (e : Expr) (except : MVarId → Bool := fun _ => false) : StateRefT Nat TermElabM Expr := do
  let nextParamIdx ← get
  let (e, nextParamIdx) ← levelMVarToParam e nextParamIdx except
  set nextParamIdx
  return e

/--
  Auxiliary method for creating fresh binder names.
  Do not confuse with the method for creating fresh free/meta variable ids. -/
def mkFreshBinderName [Monad m] [MonadQuotation m] : m Name :=
  withFreshMacroScope <| MonadQuotation.addMacroScope `x

/--
  Auxiliary method for creating a `Syntax.ident` containing
  a fresh name. This method is intended for creating fresh binder names.
  It is just a thin layer on top of `mkFreshUserName`. -/
def mkFreshIdent [Monad m] [MonadQuotation m] (ref : Syntax) : m Syntax :=
  return mkIdentFrom ref (← mkFreshBinderName)

private def applyAttributesCore
    (declName : Name) (attrs : Array Attribute)
    (applicationTime? : Option AttributeApplicationTime) : TermElabM Unit :=
  for attr in attrs do
    let env ← getEnv
    match getAttributeImpl env attr.name with
    | Except.error errMsg => throwError errMsg
    | Except.ok attrImpl  =>
      match applicationTime? with
      | none => attrImpl.add declName attr.stx attr.kind
      | some applicationTime =>
        if applicationTime == attrImpl.applicationTime then
          attrImpl.add declName attr.stx attr.kind

/-- Apply given attributes **at** a given application time -/
def applyAttributesAt (declName : Name) (attrs : Array Attribute) (applicationTime : AttributeApplicationTime) : TermElabM Unit :=
  applyAttributesCore declName attrs applicationTime

def applyAttributes (declName : Name) (attrs : Array Attribute) : TermElabM Unit :=
  applyAttributesCore declName attrs none

def mkTypeMismatchError (header? : Option String) (e : Expr) (eType : Expr) (expectedType : Expr) : TermElabM MessageData := do
  let header : MessageData := match header? with
    | some header => m!"{header} "
    | none        => m!"type mismatch{indentExpr e}\n"
  return m!"{header}{← mkHasTypeButIsExpectedMsg eType expectedType}"

def throwTypeMismatchError (header? : Option String) (expectedType : Expr) (eType : Expr) (e : Expr)
    (f? : Option Expr := none) (extraMsg? : Option MessageData := none) : TermElabM α := do
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

abbrev M := MonadCacheT Expr Unit (OptionT TermElabM)

/-- See `containsPostponedTerm` -/
partial def visit (e : Expr) : M Unit := do
  checkCache e fun _ => do
    match e with
    | Expr.forallE _ d b _   => visit d; visit b
    | Expr.lam _ d b _       => visit d; visit b
    | Expr.letE _ t v b _    => visit t; visit v; visit b
    | Expr.app f a _         => visit f; visit a
    | Expr.mdata _ b _       => visit b
    | Expr.proj _ _ b _      => visit b
    | Expr.fvar fvarId ..    =>
      match (← getLocalDecl fvarId) with
      | LocalDecl.cdecl .. => return ()
      | LocalDecl.ldecl (value := v) .. => visit v
    | Expr.mvar mvarId ..    =>
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
def containsPendingMVar (e : Expr) : TermElabM Bool := do
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
-/
def synthesizeInstMVarCore (instMVar : MVarId) (maxResultSize? : Option Nat := none) : TermElabM Bool := do
  let instMVarDecl ← getMVarDecl instMVar
  let type := instMVarDecl.type
  let type ← instantiateMVars type
  let result ← trySynthInstance type maxResultSize?
  match result with
  | LOption.some val =>
    if (← isExprMVarAssigned instMVar) then
      let oldVal ← instantiateMVars (mkMVar instMVar)
      unless (← isDefEq oldVal val) do
        if (← containsPendingMVar oldVal <||> containsPendingMVar val) then
          /- If `val` or `oldVal` contains metavariables directly or indirectly (e.g., in a let-declaration),
             we return `false` to indicate we should try again later. This is very course grain since
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
          throwError "synthesized type class instance type is not definitionally equal to expected type, synthesized{indentExpr val}\nhas type{indentExpr valType}\nexpected{indentExpr oldValType}"
        throwError "synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized{indentExpr val}\ninferred{indentExpr oldVal}"
    else
      unless (← isDefEq (mkMVar instMVar) val) do
        throwError "failed to assign synthesized type class instance{indentExpr val}"
    return true
  | LOption.undef    => return false -- we will try later
  | LOption.none     =>
    if (← read).ignoreTCFailures then
      return false
    else
      throwError "failed to synthesize instance{indentExpr type}"

register_builtin_option autoLift : Bool := {
  defValue := true
  descr    := "insert monadic lifts (i.e., `liftM` and coercions) when needed"
}

register_builtin_option maxCoeSize : Nat := {
  defValue := 16
  descr    := "maximum number of instances used to construct an automatic coercion"
}

def synthesizeCoeInstMVarCore (instMVar : MVarId) : TermElabM Bool := do
  synthesizeInstMVarCore instMVar (some (maxCoeSize.get (← getOptions)))

/--
  The coercion from `α` to `Thunk α` cannot be implemented using an instance because it would
  eagerly evaluate `e`
-/
def tryCoeThunk? (expectedType : Expr) (eType : Expr) (e : Expr) : TermElabM (Option Expr) := do
  match expectedType with
  | Expr.app (Expr.const ``Thunk u _) arg _ =>
    if (← isDefEq eType arg) then
      return some (mkApp2 (mkConst ``Thunk.mk u) arg (mkSimpleThunk e))
    else
      return none
  | _ =>
    return none

def mkCoe (expectedType : Expr) (eType : Expr) (e : Expr) (f? : Option Expr := none) (errorMsgHeader? : Option String := none) : TermElabM Expr := do
  let u ← getLevel eType
  let v ← getLevel expectedType
  let coeTInstType := mkAppN (mkConst ``CoeT [u, v]) #[eType, e, expectedType]
  let mvar ← mkFreshExprMVar coeTInstType MetavarKind.synthetic
  let eNew := mkAppN (mkConst ``CoeT.coe [u, v]) #[eType, e, expectedType, mvar]
  let mvarId := mvar.mvarId!
  try
    withoutMacroStackAtErr do
      if (← synthesizeCoeInstMVarCore mvarId) then
        expandCoe eNew
      else
        -- We create an auxiliary metavariable to represent the result, because we need to execute `expandCoe`
        -- after we syntheze `mvar`
        let mvarAux ← mkFreshExprMVar expectedType MetavarKind.syntheticOpaque
        registerSyntheticMVarWithCurrRef mvarAux.mvarId! (SyntheticMVarKind.coe errorMsgHeader? eNew expectedType eType e f?)
        return mvarAux
  catch
    | Exception.error _ msg => throwTypeMismatchError errorMsgHeader? expectedType eType e f? msg
    | _                     => throwTypeMismatchError errorMsgHeader? expectedType eType e f?

/--
  Try to apply coercion to make sure `e` has type `expectedType`.
  Relevant definitions:
  ```
  class CoeT (α : Sort u) (a : α) (β : Sort v)
  abbrev coe {α : Sort u} {β : Sort v} (a : α) [CoeT α a β] : β
  ```
-/
private def tryCoe (errorMsgHeader? : Option String) (expectedType : Expr) (eType : Expr) (e : Expr) (f? : Option Expr) : TermElabM Expr := do
  if (← isDefEq expectedType eType) then
    return e
  else match (← tryCoeThunk? expectedType eType e) with
    | some r => return r
    | none   => trace[Elab.coe] "adding coercion for {e} : {eType} =?= {expectedType}"; mkCoe expectedType eType e f? errorMsgHeader?

/-- Return `some (m, α)` if `type` can be reduced to an application of the form `m α` using `[reducible]` transparency. -/
def isTypeApp? (type : Expr) : TermElabM (Option (Expr × Expr)) := do
  let type ← withReducible <| whnf type
  match type with
  | Expr.app m α _ => return some ((← instantiateMVars m), (← instantiateMVars α))
  | _              => return none

/-- Helper method used to implement auto-lift and coercions -/
private def synthesizeInst (type : Expr) : TermElabM Expr := do
  let type ← instantiateMVars type
  match (← trySynthInstance type) with
  | LOption.some val => return val
  -- Note that `ignoreTCFailures` is not checked here since it must return a result.
  | LOption.undef    => throwError "failed to synthesize instance{indentExpr type}"
  | LOption.none     => throwError "failed to synthesize instance{indentExpr type}"

/--
  Return `true` if `type` is of the form `m α` where `m` is a `Monad`.
  Note that we reduce `type` using transparency `[reducible]`.
-/
def isMonadApp (type : Expr) : TermElabM Bool := do
  let some (m, _) ← isTypeApp? type | return false
  return (← isMonad? m) |>.isSome

/--
Try coercions and monad lifts to make sure `e` has type `expectedType`.

If `expectedType` is of the form `n β`, we try monad lifts and other extensions.
Otherwise, we just use the basic `tryCoe`.

Extensions for monads.

1- Try to unify `n` and `m`. If it succeeds, then we use
   ```
   coeM {m : Type u → Type v} {α β : Type u} [∀ a, CoeT α a β] [Monad m] (x : m α) : m β
   ```
   `n` must be a `Monad` to use this one.

2- If there is monad lift from `m` to `n` and we can unify `α` and `β`, we use
  ```
  liftM : ∀ {m : Type u_1 → Type u_2} {n : Type u_1 → Type u_3} [self : MonadLiftT m n] {α : Type u_1}, m α → n α
  ```
  Note that `n` may not be a `Monad` in this case. This happens quite a bit in code such as
  ```
  def g (x : Nat) : IO Nat := do
    IO.println x
    pure x

  def f {m} [MonadLiftT IO m] : m Nat :=
    g 10

  ```

3- If there is a monad lif from `m` to `n` and a coercion from `α` to `β`, we use
  ```
  liftCoeM {m : Type u → Type v} {n : Type u → Type w} {α β : Type u} [MonadLiftT m n] [∀ a, CoeT α a β] [Monad n] (x : m α) : n β
  ```

Note that approach 3 does not subsume 1 because it is only applicable if there is a coercion from `α` to `β` for all values in `α`.
This is not the case for example for `pure $ x > 0` when the expected type is `IO Bool`. The given type is `IO Prop`, and
we only have a coercion from decidable propositions.  Approach 1 works because it constructs the coercion `CoeT (m Prop) (pure $ x > 0) (m Bool)`
using the instance `pureCoeDepProp`.

Note that, approach 2 is more powerful than `tryCoe`.
Recall that type class resolution never assigns metavariables created by other modules.
Now, consider the following scenario
```lean
def g (x : Nat) : IO Nat := ...
deg h (x : Nat) : StateT Nat IO Nat := do
v ← g x;
IO.Println v;
...
```
Let's assume there is no other occurrence of `v` in `h`.
Thus, we have that the expected of `g x` is `StateT Nat IO ?α`,
and the given type is `IO Nat`. So, even if we add a coercion.
```
instance {α m n} [MonadLiftT m n] {α} : Coe (m α) (n α) := ...
```
It is not applicable because TC would have to assign `?α := Nat`.
On the other hand, TC can easily solve `[MonadLiftT IO (StateT Nat IO)]`
since this goal does not contain any metavariables. And then, we
convert `g x` into `liftM $ g x`.
-/
private def tryLiftAndCoe (errorMsgHeader? : Option String) (expectedType : Expr) (eType : Expr) (e : Expr) (f? : Option Expr) : TermElabM Expr := do
  let expectedType ← instantiateMVars expectedType
  let eType ← instantiateMVars eType
  let throwMismatch {α} : TermElabM α := throwTypeMismatchError errorMsgHeader? expectedType eType e f?
  let tryCoeSimple : TermElabM Expr :=
    tryCoe errorMsgHeader? expectedType eType e f?
  let some (n, β) ← isTypeApp? expectedType | tryCoeSimple
  let some (m, α) ← isTypeApp? eType | tryCoeSimple
  if (← isDefEq m n) then
    let some monadInst ← isMonad? n | tryCoeSimple
    try expandCoe (← mkAppOptM ``Lean.Internal.coeM #[m, α, β, none, monadInst, e]) catch _ => throwMismatch
  else if autoLift.get (← getOptions) then
    try
      -- Construct lift from `m` to `n`
      let monadLiftType ← mkAppM ``MonadLiftT #[m, n]
      let monadLiftVal  ← synthesizeInst monadLiftType
      let u_1 ← getDecLevel α
      let u_2 ← getDecLevel eType
      let u_3 ← getDecLevel expectedType
      let eNew := mkAppN (Lean.mkConst ``liftM [u_1, u_2, u_3]) #[m, n, monadLiftVal, α, e]
      let eNewType ← inferType eNew
      if (← isDefEq expectedType eNewType) then
        return eNew -- approach 2 worked
      else
        let some monadInst ← isMonad? n | tryCoeSimple
        let u ← getLevel α
        let v ← getLevel β
        let coeTInstType := Lean.mkForall `a BinderInfo.default α <| mkAppN (mkConst ``CoeT [u, v]) #[α, mkBVar 0, β]
        let coeTInstVal ← synthesizeInst coeTInstType
        let eNew ← expandCoe (mkAppN (Lean.mkConst ``Lean.Internal.liftCoeM [u_1, u_2, u_3]) #[m, n, α, β, monadLiftVal, coeTInstVal, monadInst, e])
        let eNewType ← inferType eNew
        unless (← isDefEq expectedType eNewType) do throwMismatch
        return eNew -- approach 3 worked
    catch _ =>
      /- If `m` is not a monad, then we try to use `tryCoe?`. -/
      tryCoeSimple
  else
    tryCoeSimple

/--
  If `expectedType?` is `some t`, then ensure `t` and `eType` are definitionally equal.
  If they are not, then try coercions.

  Argument `f?` is used only for generating error messages. -/
def ensureHasTypeAux (expectedType? : Option Expr) (eType : Expr) (e : Expr)
    (f? : Option Expr := none) (errorMsgHeader? : Option String := none) : TermElabM Expr := do
  match expectedType? with
  | none              => return e
  | some expectedType =>
    if (← isDefEq eType expectedType) then
      return e
    else
      tryLiftAndCoe errorMsgHeader? expectedType eType e f?

/--
  If `expectedType?` is `some t`, then ensure `t` and type of `e` are definitionally equal.
  If they are not, then try coercions. -/
def ensureHasType (expectedType? : Option Expr) (e : Expr) (errorMsgHeader? : Option String := none) : TermElabM Expr :=
  match expectedType? with
  | none => return e
  | _    => do
    let eType ← inferType e
    ensureHasTypeAux expectedType? eType e none errorMsgHeader?

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
  Log the given exception, and create an synthetic sorry for representing the failed
  elaboration step with exception `ex`.
-/
def exceptionToSorry (ex : Exception) (expectedType? : Option Expr) : TermElabM Expr := do
  let syntheticSorry ← mkSyntheticSorryFor expectedType?
  logException ex
  pure syntheticSorry

/-- If `mayPostpone == true`, throw `Expection.postpone`. -/
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

private def postponeElabTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  trace[Elab.postpone] "{stx} : {expectedType?}"
  let mvar ← mkFreshExprMVar expectedType? MetavarKind.syntheticOpaque
  registerSyntheticMVar stx mvar.mvarId! (SyntheticMVarKind.postponed (← saveContext))
  return mvar

def getSyntheticMVarDecl? (mvarId : MVarId) : TermElabM (Option SyntheticMVarDecl) :=
  return (← get).syntheticMVars.find? fun d => d.mvarId == mvarId

/--
  Create an auxiliary annotation to make sure we create a `Info` even if `e` is a metavariable.
  See `mkTermInfo`.

  We use this functions because some elaboration functions elaborate subterms that may not be immediately
  part of the resulting term. Example:
  ```
  let_mvar% ?m := b; wait_if_type_mvar% ?m; body
  ```
  If the type of `b` is not known, then `wait_if_type_mvar% ?m; body` is postponed and just return a fresh
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
  | Expr.mvar mvarId _ =>
    match (← getSyntheticMVarDecl? mvarId) with
    | some { kind := SyntheticMVarKind.tactic .., .. }    => return mvarId
    | some { kind := SyntheticMVarKind.postponed .., .. } => return mvarId
    | _                                                   => return none
  | _ => pure none

def mkTermInfo (elaborator : Name) (stx : Syntax) (e : Expr) (expectedType? : Option Expr := none) (lctx? : Option LocalContext := none) (isBinder := false) : TermElabM (Sum Info MVarId) := do
  match (← isTacticOrPostponedHole? e) with
  | some mvarId => return Sum.inr mvarId
  | none =>
    let e := removeSaveInfoAnnotation e
    return Sum.inl <| Info.ofTermInfo { elaborator, lctx := lctx?.getD (← getLCtx), expr := e, stx, expectedType?, isBinder }

def addTermInfo (stx : Syntax) (e : Expr) (expectedType? : Option Expr := none) (lctx? : Option LocalContext := none) (elaborator := Name.anonymous) (isBinder := false) : TermElabM Expr := do
  if (← read).inPattern then
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

/-
  Helper function for `elabTerm` is tries the registered elaboration functions for `stxNode` kind until it finds one that supports the syntax or
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
          | Exception.error _   _   =>
            if (← read).errToSorry then
              exceptionToSorry ex expectedType?
            else
              throw ex
          | Exception.internal id _ =>
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
              postponeElabTerm stx expectedType?
            else
              throw ex)
    catch ex => match ex with
      | Exception.internal id _ =>
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
  Return true if `stx` if a lambda abstraction containing a `{}` or `[]` binder annotation.
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
  match stx with
  | `(_)          => true
  | `(? _)        => true
  | `(? $_:ident) => true
  | _             => false

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
  | `(($_ : $_)) => true
  | _            => false

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

/--
  Return normalized expected type if it is of the form `{a : α} → β` or `[a : α] → β` and
  `blockImplicitLambda stx` is not true, else return `none`.

  Remark: implicit lambdas are not triggered by the strict implicit binder annotation `{{a : α}} → β`
-/
private def useImplicitLambda? (stx : Syntax) (expectedType? : Option Expr) : TermElabM (Option Expr) :=
  if blockImplicitLambda stx then
    return none
  else match expectedType? with
    | some expectedType => do
      if hasNoImplicitLambdaAnnotation expectedType then
        return none
      else
        let expectedType ← whnfForall expectedType
        match expectedType with
        | Expr.forallE _ _ _ c =>
          if c.binderInfo.isImplicit || c.binderInfo.isInstImplicit then
            return some expectedType
          else
            return none
        | _ => return none
    | _ => return none

private def decorateErrorMessageWithLambdaImplicitVars (ex : Exception) (impFVars : Array Expr) : TermElabM Exception := do
  match ex with
  | Exception.error ref msg =>
    if impFVars.isEmpty then
      return Exception.error ref msg
    else
      let mut msg := m!"{msg}\nthe following variables have been introduced by the implicit lambda feature"
      for impFVar in impFVars do
        let auxMsg := m!"{impFVar} : {← inferType impFVar}"
        let auxMsg ← addMessageContext auxMsg
        msg := m!"{msg}{indentD auxMsg}"
      msg := m!"{msg}\nyou can disable implict lambdas using `@` or writing a lambda expression with `\{}` or `[]` binder annotations."
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
  loop
    | type@(Expr.forallE n d b c), fvars =>
      if c.binderInfo.isExplicit then
        elabImplicitLambdaAux stx catchExPostpone type fvars
      else withFreshMacroScope do
        let n ← MonadQuotation.addMacroScope n
        withLocalDecl n c.binderInfo d fun fvar => do
          let type ← whnfForall (b.instantiate1 fvar)
          loop type (fvars.push fvar)
    | type, fvars =>
      elabImplicitLambdaAux stx catchExPostpone type fvars

/- Main loop for `elabTerm` -/
private partial def elabTermAux (expectedType? : Option Expr) (catchExPostpone : Bool) (implicitLambda : Bool) : Syntax → TermElabM Expr
  | Syntax.missing => mkSyntheticSorryFor expectedType?
  | stx => withFreshMacroScope <| withIncRecDepth do
    trace[Elab.step] "expected type: {expectedType?}, term\n{stx}"
    checkMaxHeartbeats "elaborator"
    withNestedTraces do
    let env ← getEnv
    match (← liftMacroM (expandMacroImpl? env stx)) with
    | some (decl, stxNew?) =>
      let stxNew ← liftMacroM <| liftExcept stxNew?
      withInfoContext' stx (mkInfo := mkTermInfo decl (expectedType? := expectedType?) stx) <|
        withMacroExpansion stx stxNew <|
          withRef stxNew <|
            elabTermAux expectedType? catchExPostpone implicitLambda stxNew
    | _ =>
      let implicit? ← if implicitLambda && (← read).implicitLambda then useImplicitLambda? stx expectedType? else pure none
      match implicit? with
      | some expectedType => elabImplicitLambda stx catchExPostpone expectedType
      | none              => elabUsingElabFns stx expectedType? catchExPostpone

/-- Store in the `InfoTree` that `e` is a "dot"-completion target. -/
def addDotCompletionInfo (stx : Syntax) (e : Expr) (expectedType? : Option Expr) (field? : Option Syntax := none) : TermElabM Unit := do
  addCompletionInfo <| CompletionInfo.dot { expr := e, stx, lctx := (← getLCtx), elaborator := Name.anonymous, expectedType? } (field? := field?) (expectedType? := expectedType?)

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

  If `implicitLambda == true`, then disable implicit lambdas feature for the given syntax, but not for its subterms.
  We use this flag to implement, for example, the `@` modifier. If `Context.implicitLambda == false`, then this parameter has no effect.
  -/
def elabTerm (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone := true) (implicitLambda := true) : TermElabM Expr :=
  withRef stx <| elabTermAux expectedType? catchExPostpone implicitLambda stx

def elabTermEnsuringType (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone := true) (implicitLambda := true) (errorMsgHeader? : Option String := none) : TermElabM Expr := do
  let e ← elabTerm stx expectedType? catchExPostpone implicitLambda
  withRef stx <| ensureHasType expectedType? e errorMsgHeader?

/--
  Execute `x` and then restore `syntheticMVars`, `levelNames`, `mvarErrorInfos`, and `letRecsToLift`.
  We use this combinator when we don't want the pending problems created by `x` to persist after its execution. -/
def withoutPending (x : TermElabM α) : TermElabM α := do
  let saved ← get
  try
    x
  finally
    modify fun s => { s with syntheticMVars := saved.syntheticMVars, levelNames := saved.levelNames,
                             letRecsToLift := saved.letRecsToLift, mvarErrorInfos := saved.mvarErrorInfos }

/-- Execute `x` and return `some` if no new errors were recorded or exceptions was thrown. Otherwise, return `none` -/
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
  It type class resolution cannot be executed (e.g., it is stuck because of metavariables in `type`),
  register metavariable as a pending one.
-/
def mkInstMVar (type : Expr) : TermElabM Expr := do
  let mvar ← mkFreshExprMVar type MetavarKind.synthetic
  let mvarId := mvar.mvarId!
  unless (← synthesizeInstMVarCore mvarId) do
    registerSyntheticMVarWithCurrRef mvarId SyntheticMVarKind.typeClass
  return mvar

/--
  Relevant definitions:
  ```
  class CoeSort (α : Sort u) (β : outParam (Sort v))
  ```
  -/
private def tryCoeSort (α : Expr) (a : Expr) : TermElabM Expr := do
  let β ← mkFreshTypeMVar
  let u ← getLevel α
  let v ← getLevel β
  let coeSortInstType := mkAppN (Lean.mkConst ``CoeSort [u, v]) #[α, β]
  let mvar ← mkFreshExprMVar coeSortInstType MetavarKind.synthetic
  let mvarId := mvar.mvarId!
  try
    withoutMacroStackAtErr do
      if (← synthesizeCoeInstMVarCore mvarId) then
        let result ← expandCoe <| mkAppN (Lean.mkConst ``CoeSort.coe [u, v]) #[α, β, mvar, a]
        unless (← isType result) do
          throwError "failed to coerse{indentExpr a}\nto a type, after applying `CoeSort.coe`, result is still not a type{indentExpr result}\nthis is often due to incorrect `CoeSort` instances, the synthesized value for{indentExpr coeSortInstType}\nwas{indentExpr mvar}"
        return result
      else
        throwError "type expected"
  catch
    | Exception.error _ msg => throwError "type expected\n{msg}"
    | _                     => throwError "type expected"

/--
  Make sure `e` is a type by inferring its type and making sure it is a `Expr.sort`
  or is unifiable with `Expr.sort`, or can be coerced into one. -/
def ensureType (e : Expr) : TermElabM Expr := do
  if (← isType e) then
    return e
  else
    let eType ← inferType e
    let u ← mkFreshLevelMVar
    if (← isDefEq eType (mkSort u)) then
      return e
    else
      tryCoeSort eType e

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
      let rec loop (s : SavedState) : TermElabM α := do
        try
          k
        catch
          | ex => match isAutoBoundImplicitLocalException? ex with
            | some n =>
              -- Restore state, declare `n`, and try again
              s.restore
              withLocalDecl n BinderInfo.implicit (← mkFreshTypeMVar) fun x =>
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
    go mvarIds.toList init
where
  go (mvarIds : List MVarId) (result : Array Expr) : TermElabM (Array Expr) := do
    match mvarIds with
    | [] => return result
    | mvarId :: mvarIds => do
      if (← isExprMVarAssigned mvarId) then
        go mvarIds result
      else if result.contains (mkMVar mvarId) || except mvarId then
        go mvarIds result
      else
        let mvarType := (← getMVarDecl mvarId).type
        let mvarIdsNew ← getMVars mvarType
        let mvarIdsNew := mvarIdsNew.filter fun mvarId => !result.contains (mkMVar mvarId)
        if mvarIdsNew.isEmpty then
          go  mvarIds (result.push (mkMVar mvarId))
        else
          go (mvarIdsNew.toList ++ mvarId :: mvarIds) result

/--
  Return `autoBoundImplicits ++ xs`
  This methoid throws an error if a variable in `autoBoundImplicits` depends on some `x` in `xs`.
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
          let localDecl ← getLocalDecl auto.fvarId!
          for x in xs do
            if (← localDeclDependsOn localDecl x.fvarId!) then
              throwError "invalid auto implicit argument '{auto}', it depends on explicitly provided argument '{x}'"
      return autos ++ xs
    | auto :: todo =>
      let autos ← collectUnassignedMVars (← inferType auto) autos
      go todo (autos.push auto)

/--
  Similar to `autoBoundImplicits`, but immediately if the resulting array of expressions contains metavariables,
  it immediately use `mkForallFVars` + `forallBoundedTelescope` to convert them into free variables.
  The type `type` is modified during the process if type depends on `xs`.
  We use this method to simplify the conversion of code using `autoBoundImplicitsOld` to `autoBoundImplicits`
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

/- Return true if mvarId is an auxiliary metavariable created for compiling `let rec` or it
   is delayed assigned to one. -/
def isLetRecAuxMVar (mvarId : MVarId) : TermElabM Bool := do
  trace[Elab.letrec] "mvarId: {mkMVar mvarId} letrecMVars: {(← get).letRecsToLift.map (mkMVar $ ·.mvarId)}"
  let mvarId ← getDelayedMVarRoot mvarId
  trace[Elab.letrec] "mvarId root: {mkMVar mvarId}"
  return (← get).letRecsToLift.any (·.mvarId == mvarId)

def resolveLocalName (n : Name) : TermElabM (Option (Expr × List String)) := do
  let lctx ← getLCtx
  let view := extractMacroScopes n
  let rec loop (n : Name) (projs : List String) :=
    match lctx.findFromUserName? { view with name := n }.review with
    | some decl =>
      if decl.isAuxDecl && !projs.isEmpty then
        /- We do not consider dot notation for local decls corresponding to recursive functions being defined.
           The following example would not be elaborated correctly without this case.
           ```
            def foo.aux := 1
            def foo : Nat → Nat
              | n => foo.aux -- should not be interpreted as `(foo).bar`
           ```
         -/
        none
      else
        some (decl.toExpr, projs)
    | none      => match n with
      | Name.str pre s _ => loop pre (s::projs)
      | _                => none
  return loop view.name []

/-- Return true iff `stx` is a `Syntax.ident`, and it is a local variable. -/
def isLocalIdent? (stx : Syntax) : TermElabM (Option Expr) :=
  match stx with
  | Syntax.ident _ _ val _ => do
    let r? ← resolveLocalName val
    match r? with
    | some (fvar, []) => return some fvar
    | _               => return none
  | _ => return none

/--
  Create an `Expr.const` using the given name and explicit levels.
  Remark: fresh universe metavariables are created if the constant has more universe
  parameters than `explicitLevels`. -/
def mkConst (constName : Name) (explicitLevels : List Level := []) : TermElabM Expr := do
  let cinfo ← getConstInfo constName
  if explicitLevels.length > cinfo.levelParams.length then
    throwError "too many explicit universe levels for '{constName}'"
  else
    let numMissingLevels := cinfo.levelParams.length - explicitLevels.length
    let us ← mkFreshLevelMVars numMissingLevels
    return Lean.mkConst constName (explicitLevels ++ us)

private def mkConsts (candidates : List (Name × List String)) (explicitLevels : List Level) : TermElabM (List (Expr × List String)) := do
  candidates.foldlM (init := []) fun result (constName, projs) => do
    -- TODO: better suppor for `mkConst` failure. We may want to cache the failures, and report them if all candidates fail.
   let const ← mkConst constName explicitLevels
   return (const, projs) :: result

def resolveName (stx : Syntax) (n : Name) (preresolved : List (Name × List String)) (explicitLevels : List Level) (expectedType? : Option Expr := none) : TermElabM (List (Expr × List String)) := do
  addCompletionInfo <| CompletionInfo.id stx stx.getId (danglingDot := false) (← getLCtx) expectedType?
  if let some (e, projs) ← resolveLocalName n then
    unless explicitLevels.isEmpty do
      throwError "invalid use of explicit universe parameters, '{e}' is a local"
    return [(e, projs)]
  -- check for section variable capture by a quotation
  let ctx ← read
  if let some (e, projs) := preresolved.findSome? fun (n, projs) => ctx.sectionFVars.find? n |>.map (·, projs) then
    return [(e, projs)]  -- section variables should shadow global decls
  if preresolved.isEmpty then
    process (← resolveGlobalName n)
  else
    process preresolved
where process (candidates : List (Name × List String)) : TermElabM (List (Expr × List String)) := do
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
  | Syntax.ident _    _      n preresolved =>
    let r ← resolveName ident n preresolved explicitLevels expectedType?
    r.mapM fun (c, fields) => do
      let ids := ident.identComponents (nFields? := fields.length)
      return (c, ids.head!, ids.tail!)
  | _ => throwError "identifier expected"

def resolveId? (stx : Syntax) (kind := "term") (withInfo := false) : TermElabM (Option Expr) :=
  match stx with
  | Syntax.ident _ _ val preresolved => do
    let rs ← try resolveName stx val preresolved [] catch _ => pure []
    let rs := rs.filter fun ⟨_, projs⟩ => projs.isEmpty
    let fs := rs.map fun (f, _) => f
    match fs with
    | []  => return none
    | [f] =>
      let f ← if withInfo then addTermInfo stx f else pure f
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

instance [MetaEval α] : MetaEval (TermElabM α) where
  eval env opts x _ := do
    let x : TermElabM α := do
      try x finally
        (← Core.getMessageLog).forM fun msg => do IO.println (← msg.toString)
    MetaEval.eval env opts (hideUnit := true) <| x.run' {}

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
def exprToSyntax (e : Expr) : TermElabM Term := do
  let result ← `(?m)
  let eType ← inferType e
  let mvar ← elabTerm result eType
  assignExprMVar mvar.mvarId! e
  return result

end Term

open Term in
def withoutModifyingStateWithInfoAndMessages [MonadControlT TermElabM m] [Monad m] (x : m α) : m α := do
  controlAt TermElabM fun runInBase => withoutModifyingStateWithInfoAndMessagesImpl <| runInBase x

builtin_initialize
  registerTraceClass `Elab.postpone
  registerTraceClass `Elab.coe
  registerTraceClass `Elab.debug

export Term (TermElabM)

end Lean.Elab
