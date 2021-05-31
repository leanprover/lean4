/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ResolveName
import Lean.Util.Sorry
import Lean.Util.ReplaceExpr
import Lean.Structure
import Lean.Meta.ExprDefEq
import Lean.Meta.AppBuilder
import Lean.Meta.SynthInstance
import Lean.Meta.CollectMVars
import Lean.Meta.Coe
import Lean.Meta.Tactic.Util
import Lean.Hygiene
import Lean.Util.RecDepth
import Lean.Elab.Log
import Lean.Elab.Level
import Lean.Elab.Attributes
import Lean.Elab.AutoBound
import Lean.Elab.InfoTree
import Lean.Elab.Open
import Lean.Elab.SetOption

namespace Lean.Elab.Term
/-
  Set isDefEq configuration for the elaborator.
  Note that we enable all approximations but `quasiPatternApprox`

  In Lean3 and Lean 4, we used to use the quasi-pattern approximation during elaboration.
  The example:
  ```
  def ex : StateT δ (StateT σ Id) σ :=
  monadLift (get : StateT σ Id σ)
  ```
  demonstrates why it produces counterintuitive behavior.
  We have the `Monad-lift` application:
  ```
  @monadLift ?m ?n ?c ?α (get : StateT σ id σ) : ?n ?α
  ```
  It produces the following unification problem when we process the expected type:
  ```
  ?n ?α =?= StateT δ (StateT σ id) σ
  ==> (approximate using first-order unification)
  ?n := StateT δ (StateT σ id)
  ?α := σ
  ```
  Then, we need to solve:
  ```
  ?m ?α =?= StateT σ id σ
  ==> instantiate metavars
  ?m σ =?= StateT σ id σ
  ==> (approximate since it is a quasi-pattern unification constraint)
  ?m := fun σ => StateT σ id σ
  ```
  Note that the constraint is not a Milner pattern because σ is in
  the local context of `?m`. We are ignoring the other possible solutions:
  ```
  ?m := fun σ' => StateT σ id σ
  ?m := fun σ' => StateT σ' id σ
  ?m := fun σ' => StateT σ id σ'
  ```

  We need the quasi-pattern approximation for elaborating recursor-like expressions (e.g., dependent `match with` expressions).

  If we had use first-order unification, then we would have produced
  the right answer: `?m := StateT σ id`

  Haskell would work on this example since it always uses
  first-order unification.
-/
def setElabConfig (cfg : Meta.Config) : Meta.Config :=
  { cfg with foApprox := true, ctxApprox := true, constApprox := false, quasiPatternApprox := false }

structure Context where
  fileName        : String
  fileMap         : FileMap
  declName?       : Option Name     := none
  macroStack      : MacroStack      := []
  currMacroScope  : MacroScope      := firstFrontendMacroScope
  /- When `mayPostpone == true`, an elaboration function may interrupt its execution by throwing `Exception.postpone`.
     The function `elabTerm` catches this exception and creates fresh synthetic metavariable `?m`, stores `?m` in
     the list of pending synthetic metavariables, and returns `?m`. -/
  mayPostpone     : Bool            := true
  /- When `errToSorry` is set to true, the method `elabTerm` catches
     exceptions and converts them into synthetic `sorry`s.
     The implementation of choice nodes and overloaded symbols rely on the fact
     that when `errToSorry` is set to false for an elaboration function `F`, then
     `errToSorry` remains `false` for all elaboration functions invoked by `F`.
     That is, it is safe to transition `errToSorry` from `true` to `false`, but
     we must not set `errToSorry` to `true` when it is currently set to `false`. -/
  errToSorry      : Bool            := true
  /- When `autoBoundImplicit` is set to true, instead of producing
     an "unknown identifier" error for unbound variables, we generate an
     internal exception. This exception is caught at `elabBinders` and
     `elabTypeWithUnboldImplicit`. Both methods add implicit declarations
     for the unbound variable and try again. -/
  autoBoundImplicit  : Bool            := false
  autoBoundImplicits : Std.PArray Expr := {}
  /-- Map from user name to internal unique name -/
  sectionVars        : NameMap Name    := {}
  /-- Map from internal name to fvar -/
  sectionFVars       : NameMap Expr    := {}
  /-- Enable/disable implicit lambdas feature. -/
  implicitLambda     : Bool            := true

/-- Saved context for postponed terms and tactics to be executed. -/
structure SavedContext where
  declName?  : Option Name
  options    : Options
  openDecls  : List OpenDecl
  macroStack : MacroStack
  errToSorry : Bool

/-- We use synthetic metavariables as placeholders for pending elaboration steps. -/
inductive SyntheticMVarKind where
  -- typeclass instance search
  | typeClass
  /- Similar to typeClass, but error messages are different.
     if `f?` is `some f`, we produce an application type mismatch error message.
     Otherwise, if `header?` is `some header`, we generate the error `(header ++ "has type" ++ eType ++ "but it is expected to have type" ++ expectedType)`
     Otherwise, we generate the error `("type mismatch" ++ e ++ "has type" ++ eType ++ "but it is expected to have type" ++ expectedType)` -/
  | coe (header? : Option String) (eNew : Expr) (expectedType : Expr) (eType : Expr) (e : Expr) (f? : Option Expr)
  -- tactic block execution
  | tactic (tacticCode : Syntax) (ctx : SavedContext)
  -- `elabTerm` call that threw `Exception.postpone` (input is stored at `SyntheticMVarDecl.ref`)
  | postponed (ctx : SavedContext)

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

inductive MVarErrorKind where
  | implicitArg (ctx : Expr)
  | hole
  | custom (msgData : MessageData)

instance : ToString MVarErrorKind where
  toString
    | MVarErrorKind.implicitArg ctx => "implicitArg"
    | MVarErrorKind.hole            => "hole"
    | MVarErrorKind.custom msg      => "custom"

structure MVarErrorInfo where
  mvarId    : MVarId
  ref       : Syntax
  kind      : MVarErrorKind

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

structure State where
  levelNames        : List Name       := []
  syntheticMVars    : List SyntheticMVarDecl := []
  mvarErrorInfos    : List MVarErrorInfo := []
  messages          : MessageLog := {}
  letRecsToLift     : List LetRecToLift := []
  infoState         : InfoState := {}
  deriving Inhabited

abbrev TermElabM := ReaderT Context $ StateRefT State MetaM
abbrev TermElab  := Syntax → Option Expr → TermElabM Expr

open Meta

instance : Inhabited (TermElabM α) where
  default := throw arbitrary

structure SavedState where
  meta   : Meta.SavedState
  «elab» : State
  deriving Inhabited

protected def saveState : TermElabM SavedState := do
  pure { meta := (← Meta.saveState), «elab» := (← get) }

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
  default := EStateM.Result.ok arbitrary arbitrary

def setMessageLog (messages : MessageLog) : TermElabM Unit :=
  modify fun s => { s with messages := messages }

def resetMessageLog : TermElabM Unit :=
  setMessageLog {}

def getMessageLog : TermElabM MessageLog :=
  return (← get).messages

/--
  Execute `x`, save resulting expression and new state.
  We remove any `Info` created by `x`.
  The info nodes are committed when we execute `applyResult`.
  We use `observing` to implement overloaded notation and decls.
  We want to save `Info` nodes for the chosen alternative.
-/
@[inline] def observing (x : TermElabM α) : TermElabM (TermElabResult α) := do
  let s ← saveState
  try
    let e ← x
    let sNew ← saveState
    s.restore (restoreInfo := true)
    pure (EStateM.Result.ok e sNew)
  catch
    | ex@(Exception.error _ _) =>
      let sNew ← saveState
      s.restore (restoreInfo := true)
      pure (EStateM.Result.error ex sNew)
    | ex@(Exception.internal id _) =>
      if id == postponeExceptionId then
        s.restore (restoreInfo := true)
      throw ex

/--
  Apply the result/exception and state captured with `observing`.
  We use this method to implement overloaded notation and symbols. -/
@[inline] def applyResult (result : TermElabResult α) : TermElabM α :=
  match result with
  | EStateM.Result.ok a r     => do r.restore (restoreInfo := true); pure a
  | EStateM.Result.error ex r => do r.restore (restoreInfo := true); throw ex

/--
  Execute `x`, but keep state modifications only if `x` did not postpone.
  This method is useful to implement elaboration functions that cannot decide whether
  they need to postpone or not without updating the state. -/
def commitIfDidNotPostpone (x : TermElabM α) : TermElabM α := do
  -- We just reuse the implementation of `observing` and `applyResult`.
  let r ← observing x
  applyResult r

/--
  Execute `x` but discard changes performed at `Term.State` and `Meta.State`.
  Recall that the environment is at `Core.State`. Thus, any updates to it will
  be preserved. This method is useful for performing computations where all
  metavariable must be resolved or discarded. -/
def withoutModifyingElabMetaState (x : TermElabM α) : TermElabM α := do
  let s ← get
  let sMeta ← getThe Meta.State
  try
    x
  finally
    set s
    set sMeta

def getLevelNames : TermElabM (List Name) :=
  return (← get).levelNames

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

instance : MonadLog TermElabM where
  getRef      := getRef
  getFileMap  := return (← read).fileMap
  getFileName := return (← read).fileName
  logMessage msg := do
    let ctx ← readThe Core.Context
    let msg := { msg with data := MessageData.withNamingContext { currNamespace := ctx.currNamespace, openDecls := ctx.openDecls } msg.data };
    modify fun s => { s with messages := s.messages.add msg }

protected def getCurrMacroScope : TermElabM MacroScope := do pure (← read).currMacroScope
protected def getMainModule     : TermElabM Name := do pure (← getEnv).mainModule

@[inline] protected def withFreshMacroScope (x : TermElabM α) : TermElabM α := do
  let fresh ← modifyGetThe Core.State (fun st => (st.nextMacroScope, { st with nextMacroScope := st.nextMacroScope + 1 }))
  withReader (fun ctx => { ctx with currMacroScope := fresh }) x

instance : MonadQuotation TermElabM where
  getCurrMacroScope   := Term.getCurrMacroScope
  getMainModule       := Term.getMainModule
  withFreshMacroScope := Term.withFreshMacroScope

instance : MonadInfoTree TermElabM where
  getInfoState      := return (← get).infoState
  modifyInfoState f := modify fun s => { s with infoState := f s.infoState }

unsafe def mkTermElabAttributeUnsafe : IO (KeyedDeclsAttribute TermElab) :=
  mkElabAttribute TermElab `Lean.Elab.Term.termElabAttribute `builtinTermElab `termElab `Lean.Parser.Term `Lean.Elab.Term.TermElab "term"

@[implementedBy mkTermElabAttributeUnsafe]
constant mkTermElabAttribute : IO (KeyedDeclsAttribute TermElab)

builtin_initialize termElabAttribute : KeyedDeclsAttribute TermElab ← mkTermElabAttribute

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
  | getOp     (ref : Syntax) (idx : Syntax)

def LVal.getRef : LVal → Syntax
  | LVal.fieldIdx ref _    => ref
  | LVal.fieldName ref ..  => ref
  | LVal.getOp ref _       => ref

def LVal.isFieldName : LVal → Bool
  | LVal.fieldName .. => true
  | _ => false

instance : ToString LVal where
  toString
    | LVal.fieldIdx _ i     => toString i
    | LVal.fieldName _ n .. => n
    | LVal.getOp _ idx      => "[" ++ toString idx ++ "]"

def getDeclName? : TermElabM (Option Name) := return (← read).declName?
def getLetRecsToLift : TermElabM (List LetRecToLift) := return (← get).letRecsToLift
def isExprMVarAssigned (mvarId : MVarId) : TermElabM Bool := return (← getMCtx).isExprAssigned mvarId
def getMVarDecl (mvarId : MVarId) : TermElabM MetavarDecl := return (← getMCtx).getDecl mvarId
def assignLevelMVar (mvarId : MVarId) (val : Level) : TermElabM Unit := modifyThe Meta.State fun s => { s with mctx := s.mctx.assignLevel mvarId val }

def withDeclName (name : Name) (x : TermElabM α) : TermElabM α :=
  withReader (fun ctx => { ctx with declName? := name }) x

def setLevelNames (levelNames : List Name) : TermElabM Unit :=
  modify fun s => { s with levelNames := levelNames }

def withLevelNames (levelNames : List Name) (x : TermElabM α) : TermElabM α := do
  let levelNamesSaved ← getLevelNames
  setLevelNames levelNames
  try x finally setLevelNames levelNamesSaved

def withoutErrToSorry (x : TermElabM α) : TermElabM α :=
  withReader (fun ctx => { ctx with errToSorry := false }) x

/-- For testing `TermElabM` methods. The #eval command will sign the error. -/
def throwErrorIfErrors : TermElabM Unit := do
  if (← get).messages.hasErrors then
    throwError "Error(s)"

@[inline] def traceAtCmdPos (cls : Name) (msg : Unit → MessageData) : TermElabM Unit :=
withRef Syntax.missing $ trace cls msg

def ppGoal (mvarId : MVarId) : TermElabM Format :=
  Meta.ppGoal mvarId

open Level (LevelElabM)

def liftLevelM (x : LevelElabM α) : TermElabM α := do
  let ctx ← read
  let ref ← getRef
  let mctx ← getMCtx
  let ngen ← getNGen
  let lvlCtx : Level.Context := { options := (← getOptions), ref := ref, autoBoundImplicit := ctx.autoBoundImplicit }
  match (x lvlCtx).run { ngen := ngen, mctx := mctx, levelNames := (← getLevelNames) } with
  | EStateM.Result.ok a newS  => setMCtx newS.mctx; setNGen newS.ngen; setLevelNames newS.levelNames; pure a
  | EStateM.Result.error ex _ => throw ex

def elabLevel (stx : Syntax) : TermElabM Level :=
  liftLevelM $ Level.elabLevel stx

/- Elaborate `x` with `stx` on the macro stack -/
@[inline] def withMacroExpansion (beforeStx afterStx : Syntax) (x : TermElabM α) : TermElabM α :=
  withMacroExpansionInfo beforeStx afterStx do
    withReader (fun ctx => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

/-
  Add the given metavariable to the list of pending synthetic metavariables.
  The method `synthesizeSyntheticMVars` is used to process the metavariables on this list. -/
def registerSyntheticMVar (stx : Syntax) (mvarId : MVarId) (kind : SyntheticMVarKind) : TermElabM Unit := do
  modify fun s => { s with syntheticMVars := { mvarId := mvarId, stx := stx, kind := kind } :: s.syntheticMVars }

def registerSyntheticMVarWithCurrRef (mvarId : MVarId) (kind : SyntheticMVarKind) : TermElabM Unit := do
  registerSyntheticMVar (← getRef) mvarId kind

def registerMVarErrorHoleInfo (mvarId : MVarId) (ref : Syntax) : TermElabM Unit := do
  modify fun s => { s with mvarErrorInfos := { mvarId := mvarId, ref := ref, kind := MVarErrorKind.hole } :: s.mvarErrorInfos }

def registerMVarErrorImplicitArgInfo (mvarId : MVarId) (ref : Syntax) (app : Expr) : TermElabM Unit := do
  modify fun s => { s with mvarErrorInfos := { mvarId := mvarId, ref := ref, kind := MVarErrorKind.implicitArg app } :: s.mvarErrorInfos }

def registerMVarErrorCustomInfo (mvarId : MVarId) (ref : Syntax) (msgData : MessageData) : TermElabM Unit := do
  modify fun s => { s with mvarErrorInfos := { mvarId := mvarId, ref := ref, kind := MVarErrorKind.custom msgData } :: s.mvarErrorInfos }

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
  if (← get).messages.hasErrors then
    throwAbortTerm
  else
    throwError m

def MVarErrorInfo.logError (mvarErrorInfo : MVarErrorInfo) (extraMsg? : Option MessageData) : TermElabM Unit := do
  match mvarErrorInfo.kind with
  | MVarErrorKind.implicitArg app => do
    let app ← instantiateMVars app
    let msg : MessageData := m!"don't know how to synthesize implicit argument{indentExpr app.setAppPPExplicitForExposingMVars}"
    let msg := msg ++ Format.line ++ "context:" ++ Format.line ++ MessageData.ofGoal mvarErrorInfo.mvarId
    logErrorAt mvarErrorInfo.ref (appendExtra msg)
  | MVarErrorKind.hole => do
    let msg : MessageData := "don't know how to synthesize placeholder"
    let msg := msg ++ Format.line ++ "context:" ++ Format.line ++ MessageData.ofGoal mvarErrorInfo.mvarId
    logErrorAt mvarErrorInfo.ref (MessageData.tagged `Elab.synthPlaceholder <| appendExtra msg)
  | MVarErrorKind.custom msg =>
    logErrorAt mvarErrorInfo.ref (appendExtra msg)
where
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
  let s ← get
  let hasOtherErrors := s.messages.hasErrors
  let mut hasNewErrors := false
  let mut alreadyVisited : NameSet := {}
  for mvarErrorInfo in s.mvarErrorInfos do
    let mvarId := mvarErrorInfo.mvarId
    unless alreadyVisited.contains mvarId do
      alreadyVisited := alreadyVisited.insert mvarId
      let foundError ← withMVarContext mvarId do
        /- The metavariable `mvarErrorInfo.mvarId` may have been assigned or
           delayed assigned to another metavariable that is unassigned. -/
        let mvarDeps ← getMVars (mkMVar mvarId)
        if mvarDeps.any pendingMVarIds.contains then do
          unless hasOtherErrors do
            mvarErrorInfo.logError extraMsg?
          pure true
        else
          pure false
      if foundError then
        hasNewErrors := true
  return hasNewErrors

/-- Ensure metavariables registered using `registerMVarErrorInfos` (and used in the given declaration) have been assigned. -/
def ensureNoUnassignedMVars (decl : Declaration) : TermElabM Unit := do
  let pendingMVarIds ← getMVarsAtDecl decl
  if (← logUnassignedUsingErrorInfos pendingMVarIds) then
    throwAbortCommand

/-
  Execute `x` without allowing it to postpone elaboration tasks.
  That is, `tryPostpone` is a noop. -/
@[inline] def withoutPostponing (x : TermElabM α) : TermElabM α :=
  withReader (fun ctx => { ctx with mayPostpone := false }) x

/-- Creates syntax for `(` <ident> `:` <type> `)` -/
def mkExplicitBinder (ident : Syntax) (type : Syntax) : Syntax :=
  mkNode ``Lean.Parser.Term.explicitBinder #[mkAtom "(", mkNullNode #[ident], mkNullNode #[mkAtom ":", type], mkNullNode, mkAtom ")"]

/--
  Convert unassigned universe level metavariables into parameters.
  The new parameter names are of the form `u_i` where `i >= nextParamIdx`.
  The method returns the updated expression and new `nextParamIdx`.

  Remark: we make sure the generated parameter names do not clash with the universes at `ctx.levelNames`. -/
def levelMVarToParam (e : Expr) (nextParamIdx : Nat := 1) : TermElabM (Expr × Nat) := do
  let mctx ← getMCtx
  let levelNames ← getLevelNames
  let r := mctx.levelMVarToParam (fun n => levelNames.elem n) e `u nextParamIdx
  setMCtx r.mctx
  pure (r.expr, r.nextParamIdx)

/-- Variant of `levelMVarToParam` where `nextParamIdx` is stored in a state monad. -/
def levelMVarToParam' (e : Expr) : StateRefT Nat TermElabM Expr := do
  let nextParamIdx ← get
  let (e, nextParamIdx) ← levelMVarToParam e nextParamIdx
  set nextParamIdx
  pure e

/--
  Auxiliary method for creating fresh binder names.
  Do not confuse with the method for creating fresh free/meta variable ids. -/
def mkFreshBinderName [Monad m] [MonadQuotation m] : m Name :=
  withFreshMacroScope $ MonadQuotation.addMacroScope `x

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
  | some f => Meta.throwAppTypeMismatch f e extraMsg

@[inline] def withoutMacroStackAtErr (x : TermElabM α) : TermElabM α :=
  withTheReader Core.Context (fun (ctx : Core.Context) => { ctx with options := pp.macroStack.set ctx.options false }) x

/- Try to synthesize metavariable using type class resolution.
   This method assumes the local context and local instances of `instMVar` coincide
   with the current local context and local instances.
   Return `true` if the instance was synthesized successfully, and `false` if
   the instance contains unassigned metavariables that are blocking the type class
   resolution procedure. Throw an exception if resolution or assignment irrevocably fails. -/
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
        let oldValType ← inferType oldVal
        let valType ← inferType val
        unless (← isDefEq oldValType valType) do
          throwError "synthesized type class instance type is not definitionally equal to expected type, synthesized{indentExpr val}\nhas type{indentExpr valType}\nexpected{indentExpr oldValType}"
        throwError "synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized{indentExpr val}\ninferred{indentExpr oldVal}"
    else
      unless (← isDefEq (mkMVar instMVar) val) do
        throwError "failed to assign synthesized type class instance{indentExpr val}"
    pure true
  | LOption.undef    => pure false -- we will try later
  | LOption.none     => throwError "failed to synthesize instance{indentExpr type}"

register_builtin_option autoLift : Bool := {
  defValue := true
  descr    := "insert monadic lifts (i.e., `liftM` and `liftCoeM`) when needed"
}

register_builtin_option maxCoeSize : Nat := {
  defValue := 16
  descr    := "maximum number of instances used to construct an automatic coercion"
}

def synthesizeCoeInstMVarCore (instMVar : MVarId) : TermElabM Bool := do
  synthesizeInstMVarCore instMVar (some (maxCoeSize.get (← getOptions)))

/-
The coercion from `α` to `Thunk α` cannot be implemented using an instance because it would
eagerly evaluate `e` -/
def tryCoeThunk? (expectedType : Expr) (eType : Expr) (e : Expr) : TermElabM (Option Expr) := do
  match expectedType with
  | Expr.app (Expr.const ``Thunk u _) arg _ =>
    if (← isDefEq eType arg) then
      pure (some (mkApp2 (mkConst ``Thunk.mk u) arg (mkSimpleThunk e)))
    else
      pure none
  | _ =>
    pure none

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
    | none   =>
      let u ← getLevel eType
      let v ← getLevel expectedType
      let coeTInstType := mkAppN (mkConst ``CoeT [u, v]) #[eType, e, expectedType]
      let mvar ← mkFreshExprMVar coeTInstType MetavarKind.synthetic
      let eNew := mkAppN (mkConst ``coe [u, v]) #[eType, expectedType, e, mvar]
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

def isTypeApp? (type : Expr) : TermElabM (Option (Expr × Expr)) := do
  let type ← withReducible $ whnf type
  match type with
  | Expr.app m α _ => pure (some ((← instantiateMVars m), (← instantiateMVars α)))
  | _              => pure none

def synthesizeInst (type : Expr) : TermElabM Expr := do
  let type ← instantiateMVars type
  match (← trySynthInstance type) with
  | LOption.some val => pure val
  | LOption.undef    => throwError "failed to synthesize instance{indentExpr type}"
  | LOption.none     => throwError "failed to synthesize instance{indentExpr type}"

def isMonadApp (type : Expr) : TermElabM Bool := do
  let some (m, _) ← isTypeApp? type | pure false
  return (← isMonad? m) |>.isSome

/--
  Try to coerce `a : α` into `m β` by first coercing `a : α` into ‵β`, and then using `pure`.
  The method is only applied if `α` is not monadic (e.g., `Nat → IO Unit`), and the head symbol
  of the resulting type is not a metavariable (e.g., `?m Unit` or `Bool → ?m Nat`).

  The main limitation of the approach above is polymorphic code. As usual, coercions and polymorphism
  do not interact well. In the example above, the lift is successfully applied to `true`, `false` and `!y`
  since none of them is polymorphic
  ```
  def f (x : Bool) : IO Bool := do
  let y ← if x == 0 then IO.println "hello"; true else false;
  !y
  ```
  On the other hand, the following fails since `+` is polymorphic
  ```
  def f (x : Bool) : IO Nat := do
  IO.prinln x
  x + x  -- Error: failed to synthesize `Add (IO Nat)`
  ```
-/
private def tryPureCoe? (errorMsgHeader? : Option String) (m β α a : Expr) : TermElabM (Option Expr) :=
  commitWhenSome? do
    let doIt : TermElabM (Option Expr) := do
      try
        let aNew ← tryCoe errorMsgHeader? β α a none
        let aNew ← mkPure m aNew
        pure (some aNew)
      catch _ =>
        pure none
    forallTelescope α fun _ α => do
      if (← isMonadApp α) then
        pure none
      else if !α.getAppFn.isMVar  then
        doIt
      else
        pure none

/-
Try coercions and monad lifts to make sure `e` has type `expectedType`.

If `expectedType` is of the form `n β`, we try monad lifts and other extensions.
Otherwise, we just use the basic `tryCoe`.

Extensions for monads.

Given an expected type of the form `n β`, if `eType` is of the form `α`, but not `m α`

1 - Try to coerce ‵α` into ‵β`, and use `pure` to lift it to `n α`.
    It only works if `n` implements `Pure`

If `eType` is of the form `m α`. We use the following approaches.

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
  let tryPureCoeAndSimple : TermElabM Expr := do
    if autoLift.get (← getOptions) then
      match (← tryPureCoe? errorMsgHeader? n β eType e) with
      | some eNew => pure eNew
      | none      => tryCoeSimple
    else
      tryCoeSimple
  let some (m, α) ← isTypeApp? eType | tryPureCoeAndSimple
  if (← isDefEq m n) then
    let some monadInst ← isMonad? n | tryCoeSimple
    try expandCoe (← mkAppOptM ``coeM #[m, α, β, none, monadInst, e]) catch _ => throwMismatch
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
        let coeTInstType := Lean.mkForall `a BinderInfo.default α $ mkAppN (mkConst ``CoeT [u, v]) #[α, mkBVar 0, β]
        let coeTInstVal ← synthesizeInst coeTInstType
        let eNew ← expandCoe (← mkAppN (Lean.mkConst ``liftCoeM [u_1, u_2, u_3]) #[m, n, α, β, monadLiftVal, coeTInstVal, monadInst, e])
        let eNewType ← inferType eNew
        unless (← isDefEq expectedType eNewType) do throwMismatch
        return eNew -- approach 3 worked
    catch _ =>
      /-
        If `m` is not a monad, then we try to use `tryPureCoe?` and then `tryCoe?`.
        Otherwise, we just try `tryCoe?`.
      -/
      match (← isMonad? m) with
      | none   => tryPureCoeAndSimple
      | some _ => tryCoeSimple
  else
    tryCoeSimple

/--
  If `expectedType?` is `some t`, then ensure `t` and `eType` are definitionally equal.
  If they are not, then try coercions.

  Argument `f?` is used only for generating error messages. -/
def ensureHasTypeAux (expectedType? : Option Expr) (eType : Expr) (e : Expr)
    (f? : Option Expr := none) (errorMsgHeader? : Option String := none) : TermElabM Expr := do
  match expectedType? with
  | none              => pure e
  | some expectedType =>
    if (← isDefEq eType expectedType) then
      pure e
    else
      tryLiftAndCoe errorMsgHeader? expectedType eType e f?

/--
  If `expectedType?` is `some t`, then ensure `t` and type of `e` are definitionally equal.
  If they are not, then try coercions. -/
def ensureHasType (expectedType? : Option Expr) (e : Expr) (errorMsgHeader? : Option String := none) : TermElabM Expr :=
  match expectedType? with
  | none => pure e
  | _    => do
    let eType ← inferType e
    ensureHasTypeAux expectedType? eType e none errorMsgHeader?

private def mkSyntheticSorryFor (expectedType? : Option Expr) : TermElabM Expr := do
  let expectedType ← match expectedType? with
    | none              => mkFreshTypeMVar
    | some expectedType => pure expectedType
  mkSyntheticSorry expectedType

private def exceptionToSorry (ex : Exception) (expectedType? : Option Expr) : TermElabM Expr := do
  let syntheticSorry ← mkSyntheticSorryFor expectedType?
  logException ex
  pure syntheticSorry

/-- If `mayPostpone == true`, throw `Expection.postpone`. -/
def tryPostpone : TermElabM Unit := do
  if (← read).mayPostpone then
    throwPostpone

/-- If `mayPostpone == true` and `e`'s head is a metavariable, throw `Exception.postpone`. -/
def tryPostponeIfMVar (e : Expr) : TermElabM Unit := do
  if e.getAppFn.isMVar then
    let e ← instantiateMVars e
    if e.getAppFn.isMVar then
      tryPostpone

def tryPostponeIfNoneOrMVar (e? : Option Expr) : TermElabM Unit :=
  match e? with
  | some e => tryPostponeIfMVar e
  | none   => tryPostpone

def tryPostponeIfHasMVars (expectedType? : Option Expr) (msg : String) : TermElabM Expr := do
  tryPostponeIfNoneOrMVar expectedType?
  let some expectedType ← pure expectedType? |
    throwError "{msg}, expected type must be known"
  let expectedType ← instantiateMVars expectedType
  if expectedType.hasExprMVar then
    tryPostpone
    throwError "{msg}, expected type contains metavariables{indentExpr expectedType}"
  pure expectedType

private def saveContext : TermElabM SavedContext :=
  return {
    macroStack := (← read).macroStack
    declName?  := (← read).declName?
    options    := (← getOptions)
    openDecls  := (← getOpenDecls)
    errToSorry := (← read).errToSorry
  }

def withSavedContext (savedCtx : SavedContext) (x : TermElabM α) : TermElabM α := do
  withReader (fun ctx => { ctx with declName? := savedCtx.declName?, macroStack := savedCtx.macroStack, errToSorry := savedCtx.errToSorry }) <|
    withTheReader Core.Context (fun ctx => { ctx with options := savedCtx.options, openDecls := savedCtx.openDecls })
      x

private def postponeElabTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  trace[Elab.postpone] "{stx} : {expectedType?}"
  let mvar ← mkFreshExprMVar expectedType? MetavarKind.syntheticOpaque
  let ctx ← read
  registerSyntheticMVar stx mvar.mvarId! (SyntheticMVarKind.postponed (← saveContext))
  pure mvar

/-
  Helper function for `elabTerm` is tries the registered elaboration functions for `stxNode` kind until it finds one that supports the syntax or
  an error is found. -/
private def elabUsingElabFnsAux (s : SavedState) (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone : Bool)
    : List TermElab → TermElabM Expr
  | []                => do throwError "unexpected syntax{indentD stx}"
  | (elabFn::elabFns) => do
    try
      elabFn stx expectedType?
    catch ex => match ex with
      | Exception.error ref msg =>
        if (← read).errToSorry then
          exceptionToSorry ex expectedType?
        else
          throw ex
      | Exception.internal id _ =>
        if (← read).errToSorry && id == abortTermExceptionId then
          exceptionToSorry ex expectedType?
        else if id == unsupportedSyntaxExceptionId then
          s.restore
          elabUsingElabFnsAux s stx expectedType? catchExPostpone elabFns
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
            throw ex

private def elabUsingElabFns (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone : Bool) : TermElabM Expr := do
  let s ← saveState
  let table := termElabAttribute.ext.getState (← getEnv) |>.table
  let k := stx.getKind
  match table.find? k with
  | some elabFns => elabUsingElabFnsAux s stx expectedType? catchExPostpone elabFns
  | none         => throwError "elaboration function for '{k}' has not been implemented{indentD stx}"

instance : MonadMacroAdapter TermElabM where
  getCurrMacroScope := getCurrMacroScope
  getNextMacroScope := return (← getThe Core.State).nextMacroScope
  setNextMacroScope next := modifyThe Core.State fun s => { s with nextMacroScope := next }

private def isExplicit (stx : Syntax) : Bool :=
  match stx with
  | `(@$f) => true
  | _      => false

private def isExplicitApp (stx : Syntax) : Bool :=
  stx.getKind == ``Lean.Parser.Term.app && isExplicit stx[0]

/--
  Return true if `stx` if a lambda abstraction containing a `{}` or `[]` binder annotation.
  Example: `fun {α} (a : α) => a` -/
private def isLambdaWithImplicit (stx : Syntax) : Bool :=
  match stx with
  | `(fun $binders* => $body) => binders.any fun b => b.isOfKind ``Lean.Parser.Term.implicitBinder || b.isOfKind `Lean.Parser.Term.instBinder
  | _                         => false

private partial def dropTermParens : Syntax → Syntax := fun stx =>
  match stx with
  | `(($stx)) => dropTermParens stx
  | _         => stx

private def isHole (stx : Syntax) : Bool :=
  match stx with
  | `(_)          => true
  | `(? _)        => true
  | `(? $x:ident) => true
  | _             => false

private def isTacticBlock (stx : Syntax) : Bool :=
  match stx with
  | `(by $x:tacticSeq) => true
  | _ => false

private def isNoImplicitLambda (stx : Syntax) : Bool :=
  match stx with
  | `(noImplicitLambda% $x:term) => true
  | _ => false

private def isTypeAscription (stx : Syntax) : Bool :=
  match stx with
  | `(($e : $type)) => true
  | _               => false

def mkNoImplicitLambdaAnnotation (type : Expr) : Expr :=
  mkAnnotation `noImplicitLambda type

def hasNoImplicitLambdaAnnotation (type : Expr) : Bool :=
  annotation? `noImplicitLambda type |>.isSome

/-- Block usage of implicit lambdas if `stx` is `@f` or `@f arg1 ...` or `fun` with an implicit binder annotation. -/
def blockImplicitLambda (stx : Syntax) : Bool :=
  let stx := dropTermParens stx
  -- TODO: make it extensible
  isExplicit stx || isExplicitApp stx || isLambdaWithImplicit stx || isHole stx || isTacticBlock stx ||
  isNoImplicitLambda stx || isTypeAscription stx

/--
  Return normalized expected type if it is of the form `{a : α} → β` or `[a : α] → β` and
  `blockImplicitLambda stx` is not true, else return `none`. -/
private def useImplicitLambda? (stx : Syntax) (expectedType? : Option Expr) : TermElabM (Option Expr) :=
  if blockImplicitLambda stx then
    pure none
  else match expectedType? with
    | some expectedType => do
      if hasNoImplicitLambdaAnnotation expectedType then
        pure none
      else
        let expectedType ← whnfForall expectedType
        match expectedType with
        | Expr.forallE _ _ _ c => if c.binderInfo.isExplicit then pure none else pure $ some expectedType
        | _                    => pure none
    | _         => pure none

private def decorateErrorMessageWithLambdaImplicitVars (ex : Exception) (impFVars : Array Expr) : TermElabM Exception := do
  match ex with
  | Exception.error ref msg =>
    if impFVars.isEmpty then
      return Exception.error ref msg
    else
      let mut msg := m!"{msg}\nthe following variables have been introduced by the implicit lamda feature"
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
    pure r
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
    let stxNew? ← catchInternalId unsupportedSyntaxExceptionId
      (do let newStx ← adaptMacro (getMacros env) stx; pure (some newStx))
      (fun _ => pure none)
    match stxNew? with
    | some stxNew => withMacroExpansion stx stxNew <| withRef stxNew <| elabTermAux expectedType? catchExPostpone implicitLambda stxNew
    | _ =>
      let implicit? ← if implicitLambda && (← read).implicitLambda then useImplicitLambda? stx expectedType? else pure none
      match implicit? with
      | some expectedType => elabImplicitLambda stx catchExPostpone expectedType
      | none              => elabUsingElabFns stx expectedType? catchExPostpone

def addTermInfo (stx : Syntax) (e : Expr) (expectedType? : Option Expr := none) : TermElabM Unit := do
  if (← getInfoState).enabled then
    pushInfoLeaf <| Info.ofTermInfo { lctx := (← getLCtx), expr := e, stx, expectedType? }

def getSyntheticMVarDecl? (mvarId : MVarId) : TermElabM (Option SyntheticMVarDecl) :=
  return (← get).syntheticMVars.find? fun d => d.mvarId == mvarId

def mkTermInfo (stx : Syntax) (e : Expr) (expectedType? : Option Expr := none) : TermElabM (Sum Info MVarId) := do
  let isHole? : TermElabM (Option MVarId) := do
    match e with
    | Expr.mvar mvarId _ =>
      match (← getSyntheticMVarDecl? mvarId) with
      | some { kind := SyntheticMVarKind.tactic .., .. }    => return mvarId
      | some { kind := SyntheticMVarKind.postponed .., .. } => return mvarId
      | _                                                   => return none
    | _ => pure none
  match (← isHole?) with
  | none        => return Sum.inl <| Info.ofTermInfo { lctx := (← getLCtx), expr := e, stx, expectedType? }
  | some mvarId => return Sum.inr mvarId

/-- Store in the `InfoTree` that `e` is a "dot"-completion target. -/
def addDotCompletionInfo (stx : Syntax) (e : Expr) (expectedType? : Option Expr) (field? : Option Syntax := none) : TermElabM Unit := do
  addCompletionInfo <| CompletionInfo.dot { expr := e, stx, lctx := (← getLCtx), expectedType? } (field? := field?) (expectedType? := expectedType?)

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
  withInfoContext' (withRef stx <| elabTermAux expectedType? catchExPostpone implicitLambda stx) (mkTermInfo stx (expectedType? := expectedType?))

def elabTermEnsuringType (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone := true) (implicitLambda := true) (errorMsgHeader? : Option String := none) : TermElabM Expr := do
  let e ← elabTerm stx expectedType? catchExPostpone implicitLambda
  withRef stx <| ensureHasType expectedType? e errorMsgHeader?

/-- Execute `x` and return `some` if no new errors were recorded or exceptions was thrown. Otherwise, return `none` -/
def commitIfNoErrors? (x : TermElabM α) : TermElabM (Option α) := do
  let saved ← saveState
  modify fun s => { s with messages := {} }
  try
    let a ← x
    if (← get).messages.hasErrors then
      restoreState saved
      return none
    else
      modify fun s => { s with messages := saved.elab.messages ++ s.messages }
      return a
  catch _ =>
    restoreState saved
    return none

/-- Adapt a syntax transformation to a regular, term-producing elaborator. -/
def adaptExpander (exp : Syntax → TermElabM Syntax) : TermElab := fun stx expectedType? => do
  let stx' ← exp stx
  withMacroExpansion stx stx' $ elabTerm stx' expectedType?

def mkInstMVar (type : Expr) : TermElabM Expr := do
  let mvar ← mkFreshExprMVar type MetavarKind.synthetic
  let mvarId := mvar.mvarId!
  unless (← synthesizeInstMVarCore mvarId) do
    registerSyntheticMVarWithCurrRef mvarId SyntheticMVarKind.typeClass
  pure mvar

/-
  Relevant definitions:
  ```
  class CoeSort (α : Sort u) (β : outParam (Sort v))
  abbrev coeSort {α : Sort u} {β : Sort v} (a : α) [CoeSort α β] : β
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
        expandCoe <| mkAppN (Lean.mkConst ``coeSort [u, v]) #[α, β, a, mvar]
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
    pure e
  else
    let eType ← inferType e
    let u ← mkFreshLevelMVar
    if (← isDefEq eType (mkSort u)) then
      pure e
    else
      tryCoeSort eType e

/-- Elaborate `stx` and ensure result is a type. -/
def elabType (stx : Syntax) : TermElabM Expr := do
  let u ← mkFreshLevelMVar
  let type ← elabTerm stx (mkSort u)
  withRef stx $ ensureType type

/--
  Enable auto-bound implicits, and execute `k` while catching auto bound implicit exceptions. When an exception is caught,
  a new local declaration is created, registered, and `k` is tried to be executed again. -/
partial def withAutoBoundImplicit (k : TermElabM α) : TermElabM α := do
  let flag := autoBoundImplicitLocal.get (← getOptions)
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

/--
  Return `autoBoundImplicits ++ xs.
  This methoid throws an error if a variable in `autoBoundImplicits` depends on some `x` in `xs` -/
def addAutoBoundImplicits (xs : Array Expr) : TermElabM (Array Expr) := do
  let autoBoundImplicits := (← read).autoBoundImplicits
  for auto in autoBoundImplicits do
    let localDecl ← getLocalDecl auto.fvarId!
    for x in xs do
      if (← getMCtx).localDeclDependsOn localDecl x.fvarId! then
        throwError "invalid auto implicit argument '{auto}', it depends on explicitly provided argument '{x}'"
  return autoBoundImplicits.toArray ++ xs

def mkAuxName (suffix : Name) : TermElabM Name := do
  match (← read).declName? with
  | none          => throwError "auxiliary declaration cannot be created when declaration name is not available"
  | some declName => Lean.mkAuxName (declName ++ suffix) 1

builtin_initialize registerTraceClass `Elab.letrec

/- Return true if mvarId is an auxiliary metavariable created for compiling `let rec` or it
   is delayed assigned to one. -/
def isLetRecAuxMVar (mvarId : MVarId) : TermElabM Bool := do
  trace[Elab.letrec] "mvarId: {mkMVar mvarId} letrecMVars: {(← get).letRecsToLift.map (mkMVar $ ·.mvarId)}"
  let mvarId := (← getMCtx).getDelayedRoot mvarId
  trace[Elab.letrec] "mvarId root: {mkMVar mvarId}"
  return (← get).letRecsToLift.any (·.mvarId == mvarId)

/- =======================================
       Builtin elaboration functions
   ======================================= -/

@[builtinTermElab «prop»] def elabProp : TermElab := fun _ _ =>
  return mkSort levelZero

private def elabOptLevel (stx : Syntax) : TermElabM Level :=
  if stx.isNone then
    pure levelZero
  else
    elabLevel stx[0]

@[builtinTermElab «sort»] def elabSort : TermElab := fun stx _ =>
  return mkSort (← elabOptLevel stx[1])

@[builtinTermElab «type»] def elabTypeStx : TermElab := fun stx _ =>
  return mkSort (mkLevelSucc (← elabOptLevel stx[1]))

/-
 the method `resolveName` adds a completion point for it using the given
    expected type. Thus, we propagate the expected type if `stx[0]` is an identifier.
    It doesn't "hurt" if the identifier can be resolved because the expected type is not used in this case.
    Recall that if the name resolution fails a synthetic sorry is returned.-/

@[builtinTermElab «pipeCompletion»] def elabPipeCompletion : TermElab := fun stx expectedType? => do
  let e ← elabTerm stx[0] none
  unless e.isSorry do
    addDotCompletionInfo stx e expectedType?
  throwErrorAt stx[1] "invalid field notation, identifier or numeral expected"

@[builtinTermElab «completion»] def elabCompletion : TermElab := fun stx expectedType? => do
  /- `ident.` is ambiguous in Lean, we may try to be completing a declaration name or access a "field". -/
  if stx[0].isIdent then
    /- If we can elaborate the identifier successfully, we assume it a dot-completion. Otherwise, we treat it as
       identifier completion with a dangling `.`.
       Recall that the server falls back to identifier completion when dot-completion fails. -/
    let s ← saveState
    try
      let e ← elabTerm stx[0] none
      addDotCompletionInfo stx e expectedType?
    catch _ =>
      s.restore
      addCompletionInfo <| CompletionInfo.id stx stx[0].getId (danglingDot := true) (← getLCtx) expectedType?
    throwErrorAt stx[1] "invalid field notation, identifier or numeral expected"
  else
    elabPipeCompletion stx expectedType?

@[builtinTermElab «hole»] def elabHole : TermElab := fun stx expectedType? => do
  let mvar ← mkFreshExprMVar expectedType?
  registerMVarErrorHoleInfo mvar.mvarId! stx
  pure mvar

@[builtinTermElab «syntheticHole»] def elabSyntheticHole : TermElab := fun stx expectedType? => do
  let arg  := stx[1]
  let userName := if arg.isIdent then arg.getId else Name.anonymous
  let mkNewHole : Unit → TermElabM Expr := fun _ => do
    let mvar ← mkFreshExprMVar expectedType? MetavarKind.syntheticOpaque userName
    registerMVarErrorHoleInfo mvar.mvarId! stx
    pure mvar
  if userName.isAnonymous then
    mkNewHole ()
  else
    let mctx ← getMCtx
    match mctx.findUserName? userName with
    | none => mkNewHole ()
    | some mvarId =>
      let mvar := mkMVar mvarId
      let mvarDecl ← getMVarDecl mvarId
      let lctx ← getLCtx
      if mvarDecl.lctx.isSubPrefixOf lctx then
        pure mvar
      else match mctx.getExprAssignment? mvarId with
      | some val =>
        let val ← instantiateMVars val
        if mctx.isWellFormed lctx val then
          pure val
        else
          withLCtx mvarDecl.lctx mvarDecl.localInstances do
            throwError "synthetic hole has already been defined and assigned to value incompatible with the current context{indentExpr val}"
      | none =>
        if mctx.isDelayedAssigned mvarId then
          -- We can try to improve this case if needed.
          throwError "synthetic hole has already beend defined and delayed assigned with an incompatible local context"
        else if lctx.isSubPrefixOf mvarDecl.lctx then
          let mvarNew ← mkNewHole ()
          modifyMCtx fun mctx => mctx.assignExpr mvarId mvarNew
          pure mvarNew
        else
          throwError "synthetic hole has already been defined with an incompatible local context"

private def mkTacticMVar (type : Expr) (tacticCode : Syntax) : TermElabM Expr := do
  let mvar ← mkFreshExprMVar type MetavarKind.syntheticOpaque
  let mvarId := mvar.mvarId!
  let ref ← getRef
  let declName? ← getDeclName?
  registerSyntheticMVar ref mvarId <| SyntheticMVarKind.tactic tacticCode (← saveContext)
  return mvar

@[builtinTermElab byTactic] def elabByTactic : TermElab := fun stx expectedType? =>
  match expectedType? with
  | some expectedType => mkTacticMVar expectedType stx
  | none => throwError ("invalid 'by' tactic, expected type has not been provided")

@[builtinTermElab noImplicitLambda] def elabNoImplicitLambda : TermElab := fun stx expectedType? =>
  elabTerm stx[1] (mkNoImplicitLambdaAnnotation <$> expectedType?)

def resolveLocalName (n : Name) : TermElabM (Option (Expr × List String)) := do
  let lctx ← getLCtx
  let view := extractMacroScopes n
  let rec loop (n : Name) (projs : List String) :=
    match lctx.findFromUserName? { view with name := n }.review with
    | some decl => some (decl.toExpr, projs)
    | none      => match n with
      | Name.str pre s _ => loop pre (s::projs)
      | _                => none
  return loop view.name []

/- Return true iff `stx` is a `Syntax.ident`, and it is a local variable. -/
def isLocalIdent? (stx : Syntax) : TermElabM (Option Expr) :=
  match stx with
  | Syntax.ident _ _ val _ => do
    let r? ← resolveLocalName val
    match r? with
    | some (fvar, []) => pure (some fvar)
    | _               => pure none
  | _ => pure none

/--
  Create an `Expr.const` using the given name and explicit levels.
  Remark: fresh universe metavariables are created if the constant has more universe
  parameters than `explicitLevels`. -/
def mkConst (constName : Name) (explicitLevels : List Level := []) : TermElabM Expr := do
  let cinfo ← getConstInfo constName
  if explicitLevels.length > cinfo.levelParams.length then
    throwError "too many explicit universe levels"
  else
    let numMissingLevels := cinfo.levelParams.length - explicitLevels.length
    let us ← mkFreshLevelMVars numMissingLevels
    pure $ Lean.mkConst constName (explicitLevels ++ us)

private def mkConsts (candidates : List (Name × List String)) (explicitLevels : List Level) : TermElabM (List (Expr × List String)) := do
  candidates.foldlM (init := []) fun result (constName, projs) => do
    -- TODO: better suppor for `mkConst` failure. We may want to cache the failures, and report them if all candidates fail.
   let const ← mkConst constName explicitLevels
   return (const, projs) :: result

def resolveName (stx : Syntax) (n : Name) (preresolved : List (Name × List String)) (explicitLevels : List Level) (expectedType? : Option Expr := none) : TermElabM (List (Expr × List String)) := do
  try
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
  catch ex =>
    if preresolved.isEmpty && explicitLevels.isEmpty then
      addCompletionInfo <| CompletionInfo.id stx stx.getId (danglingDot := false) (← getLCtx) expectedType?
    throw ex
where process (candidates : List (Name × List String)) : TermElabM (List (Expr × List String)) := do
  if candidates.isEmpty then
    if (← read).autoBoundImplicit && isValidAutoBoundImplicitName n then
      throwAutoBoundImplicitLocal n
    else
      throwError "unknown identifier '{Lean.mkConst n}'"
  if preresolved.isEmpty && explicitLevels.isEmpty then
    addCompletionInfo <| CompletionInfo.id stx stx.getId (danglingDot := false) (← getLCtx) expectedType?
  mkConsts candidates explicitLevels

/--
  Similar to `resolveName`, but creates identifiers for the main part and each projection with position information derived from `ident`.
  Example: Assume resolveName `v.head.bla.boo` produces `(v.head, ["bla", "boo"])`, then this method produces
  `(v.head, id, [f₁, f₂])` where `id` is an identifier for `v.head`, and `f₁` and `f₂` are identifiers for fields `"bla"` and `"boo"`. -/
def resolveName' (ident : Syntax) (explicitLevels : List Level) (expectedType? : Option Expr := none) : TermElabM (List (Expr × Syntax × List Syntax)) := do
  match ident with
  | Syntax.ident info rawStr n preresolved =>
    let r ← resolveName ident n preresolved explicitLevels expectedType?
    r.mapM fun (c, fields) => do
      let (cSstr, fields) := fields.foldr (init := (rawStr, [])) fun field (restSstr, fs) =>
        let fieldSstr := restSstr.takeRightWhile (· ≠ '.')
        ({ restSstr with stopPos := restSstr.stopPos - (fieldSstr.bsize + 1) }, (field, fieldSstr) :: fs)
      let mkIdentFromPos pos rawVal val :=
        let info := match info with
        | SourceInfo.original .. => SourceInfo.original "".toSubstring pos "".toSubstring (pos + rawVal.bsize)
        | _                      => SourceInfo.synthetic pos (pos + rawVal.bsize)
        Syntax.ident info rawVal val []
      let id := match c with
        | Expr.const id _ _ => id
        | Expr.fvar id _    => id
        | _                 => unreachable!
      let id := mkIdentFromPos (ident.getPos?.getD 0) cSstr id
      match info.getPos? with
      | none =>
        return (c, id, fields.map fun (field, _) => mkIdentFrom ident (Name.mkSimple field))
      | some pos =>
        let mut pos := pos + cSstr.bsize + 1
        let mut newFields := #[]
        for (field, fieldSstr) in fields do
          newFields := newFields.push <| mkIdentFromPos pos fieldSstr (Name.mkSimple field)
          pos := pos + fieldSstr.bsize + 1
        return (c, id, newFields.toList)
  | _ => throwError "identifier expected"

def resolveId? (stx : Syntax) (kind := "term") (withInfo := false) : TermElabM (Option Expr) :=
  match stx with
  | Syntax.ident _ _ val preresolved => do
    let rs ← try resolveName stx val preresolved [] catch _ => pure []
    let rs := rs.filter fun ⟨f, projs⟩ => projs.isEmpty
    let fs := rs.map fun (f, _) => f
    match fs with
    | []  => pure none
    | [f] =>
      if withInfo then
        addTermInfo stx f
      pure (some f)
    | _   => throwError "ambiguous {kind}, use fully qualified name, possible interpretations {fs}"
  | _ => throwError "identifier expected"

@[builtinTermElab cdot] def elabBadCDot : TermElab := fun stx _ =>
  throwError "invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)"

@[builtinTermElab strLit] def elabStrLit : TermElab := fun stx _ => do
  match stx.isStrLit? with
  | some val => pure $ mkStrLit val
  | none     => throwIllFormedSyntax

private def mkFreshTypeMVarFor (expectedType? : Option Expr) : TermElabM Expr := do
  let typeMVar ← mkFreshTypeMVar MetavarKind.synthetic
  match expectedType? with
  | some expectedType => discard <| isDefEq expectedType typeMVar
  | _                 => pure ()
  return typeMVar

@[builtinTermElab numLit] def elabNumLit : TermElab := fun stx expectedType? => do
  let val ← match stx.isNatLit? with
    | some val => pure val
    | none     => throwIllFormedSyntax
  let typeMVar ← mkFreshTypeMVarFor expectedType?
  let u ← getDecLevel typeMVar
  let mvar ← mkInstMVar (mkApp2 (Lean.mkConst ``OfNat [u]) typeMVar (mkNatLit val))
  let r := mkApp3 (Lean.mkConst ``OfNat.ofNat [u]) typeMVar (mkNatLit val) mvar
  registerMVarErrorImplicitArgInfo mvar.mvarId! stx r
  return r

@[builtinTermElab rawNatLit] def elabRawNatLit : TermElab :=  fun stx expectedType? => do
  match stx[1].isNatLit? with
  | some val => return mkNatLit val
  | none     => throwIllFormedSyntax

@[builtinTermElab scientificLit]
def elabScientificLit : TermElab := fun stx expectedType? => do
  match stx.isScientificLit? with
  | none        => throwIllFormedSyntax
  | some (m, sign, e) =>
    let typeMVar ← mkFreshTypeMVarFor expectedType?
    let u ← getDecLevel typeMVar
    let mvar ← mkInstMVar (mkApp (Lean.mkConst ``OfScientific [u]) typeMVar)
    return mkApp5 (Lean.mkConst ``OfScientific.ofScientific [u]) typeMVar mvar (mkNatLit m) (toExpr sign) (mkNatLit e)

@[builtinTermElab charLit] def elabCharLit : TermElab := fun stx _ => do
  match stx.isCharLit? with
  | some val => return mkApp (Lean.mkConst ``Char.ofNat) (mkNatLit val.toNat)
  | none     => throwIllFormedSyntax

@[builtinTermElab quotedName] def elabQuotedName : TermElab := fun stx _ =>
  match stx[0].isNameLit? with
  | some val => pure $ toExpr val
  | none     => throwIllFormedSyntax

@[builtinTermElab doubleQuotedName] def elabDoubleQuotedName : TermElab := fun stx _ => do
  match stx[1].isNameLit? with
  | some val => toExpr (← resolveGlobalConstNoOverloadWithInfo stx[1] val)
  | none     => throwIllFormedSyntax

@[builtinTermElab typeOf] def elabTypeOf : TermElab := fun stx _ => do
  inferType (← elabTerm stx[1] none)

@[builtinTermElab ensureTypeOf] def elabEnsureTypeOf : TermElab := fun stx expectedType? =>
  match stx[2].isStrLit? with
  | none     => throwIllFormedSyntax
  | some msg => do
    let refTerm ← elabTerm stx[1] none
    let refTermType ← inferType refTerm
    elabTermEnsuringType stx[3] refTermType (errorMsgHeader? := msg)

@[builtinTermElab ensureExpectedType] def elabEnsureExpectedType : TermElab := fun stx expectedType? =>
  match stx[1].isStrLit? with
  | none     => throwIllFormedSyntax
  | some msg => elabTermEnsuringType stx[2] expectedType? (errorMsgHeader? := msg)

@[builtinTermElab «open»] def elabOpen : TermElab := fun stx expectedType? => do
  try
    pushScope
    let openDecls ← elabOpenDecl stx[1]
    withTheReader Core.Context (fun ctx => { ctx with openDecls := openDecls }) do
      elabTerm stx[3] expectedType?
  finally
    popScope

@[builtinTermElab «set_option»] def elabSetOption : TermElab := fun stx expectedType? => do
  let options ← Elab.elabSetOption stx[1] stx[2]
  withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := maxRecDepth.get options, options := options }) do
    elabTerm stx[4] expectedType?

private def mkSomeContext : Context := {
  fileName      := "<TermElabM>"
  fileMap       := arbitrary
}

@[inline] def TermElabM.run (x : TermElabM α) (ctx : Context := mkSomeContext) (s : State := {}) : MetaM (α × State) :=
  withConfig setElabConfig (x ctx |>.run s)

@[inline] def TermElabM.run' (x : TermElabM α) (ctx : Context := mkSomeContext) (s : State := {}) : MetaM α :=
  (·.1) <$> x.run ctx s

@[inline] def TermElabM.toIO (x : TermElabM α)
    (ctxCore : Core.Context) (sCore : Core.State)
    (ctxMeta : Meta.Context) (sMeta : Meta.State)
    (ctx : Context) (s : State) : IO (α × Core.State × Meta.State × State) := do
  let ((a, s), sCore, sMeta) ← (x.run ctx s).toIO ctxCore sCore ctxMeta sMeta
  pure (a, sCore, sMeta, s)

instance [MetaEval α] : MetaEval (TermElabM α) where
  eval env opts x _ :=
    let x : TermElabM α := do
      try x finally
        let s ← get
        s.messages.forM fun msg => do IO.println (← msg.toString)
    MetaEval.eval env opts (hideUnit := true) $ x.run' mkSomeContext

unsafe def evalExpr (α) (typeName : Name) (value : Expr) : TermElabM α :=
  withoutModifyingEnv do
    let name ← mkFreshUserName `_tmp
    let type ← inferType value
    let type ← whnfD type
    unless type.isConstOf typeName do
      throwError "unexpected type at evalExpr{indentExpr type}"
    let decl := Declaration.defnDecl {
       name := name, levelParams := [], type := type,
       value := value, hints := ReducibilityHints.opaque,
       safety := DefinitionSafety.unsafe
    }
    ensureNoUnassignedMVars decl
    addAndCompile decl
    evalConst α name

private def throwStuckAtUniverseCnstr : TermElabM Unit := do
  -- This code assumes `entries` is not empty. Note that `processPostponed` uses `exceptionOnFailure` to guarantee this property
  let entries ← getPostponed
  let mut found : Std.HashSet (Level × Level) := {}
  let mut uniqueEntries := #[]
  for entry in entries do
    let mut lhs := entry.lhs
    let mut rhs := entry.rhs
    if Level.normLt rhs lhs then
      (lhs, rhs) := (rhs, lhs)
    unless found.contains (lhs, rhs) do
      found := found.insert (lhs, rhs)
      uniqueEntries := uniqueEntries.push entry
  for i in [1:uniqueEntries.size] do
    logErrorAt uniqueEntries[i].ref (← mkLevelStuckErrorMessage uniqueEntries[i])
  throwErrorAt uniqueEntries[0].ref (← mkLevelStuckErrorMessage uniqueEntries[0])

@[specialize] def withoutPostponingUniverseConstraints (x : TermElabM α) : TermElabM α := do
  let postponed ← getResetPostponed
  try
    let a ← x
    unless (← processPostponed (mayPostpone := false) (exceptionOnFailure := true)) do
      throwStuckAtUniverseCnstr
    setPostponed postponed
    return a
  catch ex =>
    setPostponed postponed
    throw ex

end Term

builtin_initialize
  registerTraceClass `Elab.postpone
  registerTraceClass `Elab.coe
  registerTraceClass `Elab.debug

export Term (TermElabM)

end Lean.Elab
