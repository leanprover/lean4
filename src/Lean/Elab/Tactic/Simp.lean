/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp
import Lean.Meta.Tactic.Simp.LoopProtection
import Lean.Meta.Tactic.Replace
import Lean.Meta.Hint
import Lean.Elab.BuiltinNotation
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config

namespace Lean.Elab.Tactic
open Meta
open TSyntax.Compat

declare_config_elab elabSimpConfigCore    Meta.Simp.Config
declare_config_elab elabSimpConfigCtxCore Meta.Simp.ConfigCtx
declare_config_elab elabDSimpConfigCore   Meta.DSimp.Config

inductive SimpKind where
  | simp
  | simpAll
  | dsimp
  deriving Inhabited, BEq

/--
  Implement a `simp` discharge function using the given tactic syntax code.
  Recall that `simp` dischargers are in `SimpM` which does not have access to `Term.State`.
  We need access to `Term.State` to store messages and update the info tree.
  Thus, we create an `IO.ref` to track these changes at `Term.State` when we execute `tacticCode`.
  We must set this reference with the current `Term.State` before we execute `simp` using the
  generated `Simp.Discharge`. -/
def tacticToDischarge (tacticCode : Syntax) : TacticM (IO.Ref Term.State × Simp.Discharge) := do
  let tacticCode ← `(tactic| try ($tacticCode:tacticSeq))
  let ref ← IO.mkRef (← getThe Term.State)
  let ctx ← readThe Term.Context
  let disch : Simp.Discharge := fun e => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `simp.discharger
    let s ← ref.get
    let runTac? : TermElabM (Option Expr) :=
      try
        /- We must only save messages and info tree changes. Recall that `simp` uses temporary metavariables (`withNewMCtxDepth`).
           So, we must not save references to them at `Term.State`.
        -/
        Term.withoutModifyingElabMetaStateWithInfo do
          Term.withSynthesize (postpone := .no) do
            Term.runTactic (report := false) mvar.mvarId! tacticCode .term
          let result ← instantiateMVars mvar
          if result.hasExprMVar then
            return none
          else
            return some result
      catch _ =>
        return none
    let (result?, s) ← liftM (m := MetaM) <| Term.TermElabM.run runTac? ctx s
    ref.set s
    return result?
  return (ref, disch)

inductive Simp.DischargeWrapper where
  | default
  | custom (ref : IO.Ref Term.State) (discharge : Simp.Discharge)

def Simp.DischargeWrapper.with (w : Simp.DischargeWrapper) (x : Option Simp.Discharge → TacticM α) : TacticM α := do
  match w with
  | default => x none
  | custom ref d =>
    ref.set (← getThe Term.State)
    try
      x d
    finally
      set (← ref.get)

/-- Construct a `Simp.DischargeWrapper` from the `Syntax` for a `simp` discharger. -/
private def mkDischargeWrapper (optDischargeSyntax : Syntax) : TacticM Simp.DischargeWrapper := do
  if optDischargeSyntax.isNone then
    return Simp.DischargeWrapper.default
  else
    let (ref, d) ← tacticToDischarge optDischargeSyntax[0][3]
    return Simp.DischargeWrapper.custom ref d

/-
  `optConfig` is of the form `("(" "config" ":=" term ")")?`
-/
def elabSimpConfig (optConfig : Syntax) (kind : SimpKind) : TacticM Meta.Simp.Config := do
  match kind with
  | .simp    => elabSimpConfigCore optConfig
  | .simpAll => return (← elabSimpConfigCtxCore optConfig).toConfig
  | .dsimp   => return { (← elabDSimpConfigCore optConfig) with }

inductive ResolveSimpIdResult where
  | none
  | expr (e : Expr)
  | simproc (declName : Name)
  /--
  Recall that when we declare a `simp` attribute using `register_simp_attr`, we automatically
  create a `simproc` attribute. However, if the user creates `simp` and `simproc` attributes
  programmatically, then one of them may be missing. Moreover, when we write `simp [seval]`,
  we want to retrieve both the simp and simproc sets. We want to hide from users that
  `simp` and `simproc` sets are stored in different data-structures.
  -/
  | ext  (ext₁? : Option SimpExtension) (ext₂? : Option Simp.SimprocExtension) (h : ext₁?.isSome || ext₂?.isSome)

private def resolveSimpIdTheorem? (simpArgTerm : Term) : TermElabM ResolveSimpIdResult := do
    let resolveExt (n : Name) : TermElabM ResolveSimpIdResult := do
      let ext₁? ← getSimpExtension? n
      let ext₂? ← Simp.getSimprocExtension? n
      if h : ext₁?.isSome || ext₂?.isSome then
        return .ext ext₁? ext₂? h
      else
        return .none
    match simpArgTerm with
    | `($id:ident) =>
      try
        if let some e ← Term.resolveId? simpArgTerm (withInfo := true) then
          if let some simprocDeclName ← isSimproc? e then
            return .simproc simprocDeclName
          else
            return .expr e
        else
          let name := id.getId.eraseMacroScopes
          if (← Simp.isBuiltinSimproc name) then
            return .simproc name
          else
            resolveExt name
      catch _ =>
        resolveExt id.getId.eraseMacroScopes
    | _ =>
      if let some e ← Term.elabCDotFunctionAlias? simpArgTerm then
        return .expr e
      else
        return .none
where
  isSimproc? (e : Expr) : MetaM (Option Name) := do
    let .const declName _ := e | return none
    unless (← Simp.isSimproc declName) do return none
    return some declName


/--
The result of elaborating a single `simp` argument
-/
inductive ElabSimpArgResult where
  | addEntries (entries : Array SimpEntry)
  | addSimproc («simproc» : Name) (post : Bool)
  | addLetToUnfold (fvarId : FVarId)
  | ext  (ext₁? : Option SimpExtension) (ext₂? : Option Simp.SimprocExtension) (h : ext₁?.isSome || ext₂?.isSome)
  | erase (toErase : Origin)
  | eraseSimproc (toErase : Name)
  | star
  | none -- used for example when elaboration fails

def ElabSimpArgResult.simpTheorems : ElabSimpArgResult → Array SimpTheorem
  | addEntries entries => Id.run do
    let mut thms := #[]
    for entry in entries do
      if let .thm thm := entry then
        thms := thms.push thm
    return thms
  | _ => #[]

private def elabDeclToUnfoldOrTheorem (config : Meta.ConfigWithKey) (id : Origin)
    (e : Expr) (post : Bool) (inv : Bool) (kind : SimpKind) : MetaM ElabSimpArgResult := do
  if e.isConst then
    let declName := e.constName!
    let info ← getConstVal declName
    if (← isProp info.type) then
      let thms ← mkSimpTheoremFromConst declName (post := post) (inv := inv)
      return .addEntries <| thms.map (SimpEntry.thm ·)
    else
      if inv then
        throwError "invalid '←' modifier, '{declName}' is a declaration name to be unfolded"
      if kind == .dsimp then
        return .addEntries #[.toUnfold declName]
      else
        .addEntries <$> mkSimpEntryOfDeclToUnfold declName
  else if e.isFVar then
    let fvarId := e.fvarId!
    let decl ← fvarId.getDecl
    if (← isProp decl.type) then
      let thms ← mkSimpTheoremFromExpr id #[] e (post := post) (inv := inv) (config := config)
      return .addEntries <| thms.map (SimpEntry.thm ·)
    else if !decl.isLet then
      throwError "invalid argument, variable is not a proposition or let-declaration"
    else if inv then
      throwError "invalid '←' modifier, '{e}' is a let-declaration name to be unfolded"
    else
      return .addLetToUnfold fvarId
  else
    let thms ← mkSimpTheoremFromExpr id #[] e (post := post) (inv := inv) (config := config)
    return .addEntries <| thms.map (SimpEntry.thm ·)

private def elabSimpTheorem (config : Meta.ConfigWithKey) (id : Origin) (stx : Syntax)
    (post : Bool) (inv : Bool) : TermElabM ElabSimpArgResult := do
  let thm? ← Term.withoutModifyingElabMetaStateWithInfo <| withRef stx do
    let e ← Term.elabTerm stx .none
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    if e.hasSyntheticSorry then
      return .none
    let e := e.eta
    if e.hasMVar then
      let r ← abstractMVars e
      return some (r.paramNames, r.expr)
    else
      return some (#[], e)
  if let some (levelParams, proof) := thm? then
    let thms ← mkSimpTheoremFromExpr id levelParams proof (post := post) (inv := inv) (config := config)
    return .addEntries <| thms.map (SimpEntry.thm ·)
  else
    return .none

private def elabSimpArg (indexConfig : Meta.ConfigWithKey) (eraseLocal : Bool) (kind : SimpKind)
    (arg : Syntax) : TacticM ElabSimpArgResult := withRef arg do
  try
    /-
    syntax simpPre := "↓"
    syntax simpPost := "↑"
    syntax simpLemma := (simpPre <|> simpPost)? "← "? term

    syntax simpErase := "-" ident
    -/
    if arg.getKind == ``Lean.Parser.Tactic.simpErase then
      let fvar? ← if eraseLocal then Term.isLocalIdent? arg[1] else pure none
      if let some fvar := fvar? then
        -- We use `eraseCore` because the simp theorem for the hypothesis was not added yet
        return .erase (.fvar fvar.fvarId!)
      else
        let id := arg[1]
        if let .ok declName ← observing (realizeGlobalConstNoOverloadWithInfo id) then
          if (← Simp.isSimproc declName) then
            return .eraseSimproc declName
          else
            return .erase (.decl declName)
        else
          -- If `id` could not be resolved, we should check whether it is a builtin simproc.
          -- before returning error.
          let name := id.getId.eraseMacroScopes
          if (← Simp.isBuiltinSimproc name) then
            return .eraseSimproc name
          else
            throwUnknownConstantAt id name
    else if arg.getKind == ``Lean.Parser.Tactic.simpLemma then
      let post :=
        if arg[0].isNone then
          true
        else
          arg[0][0].getKind == ``Parser.Tactic.simpPost
      let inv  := !arg[1].isNone
      let term := arg[2]
      match (← resolveSimpIdTheorem? term) with
      | .expr e  =>
        let name ← mkFreshId
        elabDeclToUnfoldOrTheorem indexConfig (.stx name arg) e post inv kind
      | .simproc declName =>
        return .addSimproc declName post
      | .ext ext₁? ext₂? h =>
        return .ext ext₁? ext₂? h
      | .none    =>
        let name ← mkFreshId
        elabSimpTheorem indexConfig (.stx name arg) term post inv
    else if arg.getKind == ``Lean.Parser.Tactic.simpStar then
      return .star
    else
      throwUnsupportedSyntax
  catch ex =>
    if (← read).recover then
      logException ex
      return .none
    else
      throw ex

/--
The result of elaborating a full array of simp arguments and applying them to the simp context.
-/
structure ElabSimpArgsResult where
  ctx      : Simp.Context
  simprocs : Simp.SimprocsArray
  /-- The elaborated simp arguments with syntax -/
  simpArgs : Array (Syntax × ElabSimpArgResult)

/-- Implements the effect of the `*` attribute. -/
private def applyStarArg (ctx : Simp.Context) : MetaM Simp.Context := do
  let mut simpTheorems := ctx.simpTheorems
  /-
  When using `zetaDelta := false`, we do not expand let-declarations when using `[*]`.
  Users must explicitly include it in the list.
  -/
  let hs ← getPropHyps
  for h in hs do
    unless simpTheorems.isErased (.fvar h) do
      simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr (config := ctx.indexConfig)
  return ctx.setSimpTheorems simpTheorems

/--
  Elaborate extra simp theorems provided to `simp`. `stx` is of the form `"[" simpTheorem,* "]"`
  If `eraseLocal == true`, then we consider local declarations when resolving names for erased theorems (`- id`),
  this option only makes sense for `simp_all` or `*` is used.
  When `recover := true`, try to recover from errors as much as possible so that users keep seeing
  the current goal.
-/
def elabSimpArgs (stx : Syntax) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) (eraseLocal : Bool)
    (kind : SimpKind) (ignoreStarArg := false) : TacticM ElabSimpArgsResult := do
  if stx.isNone then
    return { ctx, simprocs, simpArgs := #[] }
  else
    /-
    syntax simpPre := "↓"
    syntax simpPost := "↑"
    syntax simpLemma := (simpPre <|> simpPost)? "← "? term

    syntax simpErase := "-" ident
    -/
    let go := withMainContext do
      let zetaDeltaSet ← toZetaDeltaSet stx ctx
      withTrackingZetaDeltaSet zetaDeltaSet do
        let mut starArg := false -- only after * we can erase local declarations
        let mut args : Array (Syntax × ElabSimpArgResult) := #[]
        for argStx in stx[1].getSepArgs do
          let arg ← elabSimpArg ctx.indexConfig (eraseLocal || starArg) kind argStx
          starArg := !ignoreStarArg && (starArg || arg matches .star)
          args := args.push (argStx, arg)

        let mut thmsArray := ctx.simpTheorems
        let mut thms      := thmsArray[0]!
        let mut simprocs  := simprocs
        for (ref, arg) in args do
          match arg with
          | .addEntries entries =>
            for entry in entries do
              thms := thms.uneraseSimpEntry entry
              thms := thms.addSimpEntry entry
          | .addLetToUnfold fvarId =>
            thms := thms.addLetDeclToUnfold fvarId
          | .addSimproc declName post =>
            simprocs ← simprocs.add declName post
          | .erase origin =>
            -- `thms.erase` checks if the erasure is effective.
            -- We do not want this check for local hypotheses (they are added later based on `starArg`)
            if origin matches .fvar _ then
              thms := thms.eraseCore origin
            -- Nor for decls to unfold when we do auto unfolding
            else if ctx.config.autoUnfold then
              thms := thms.eraseCore origin
            else
              thms ← withRef ref <| thms.erase origin
          | .eraseSimproc name =>
            simprocs := simprocs.erase name
          | .ext simpExt? simprocExt? _ =>
            if let some simpExt := simpExt? then
              thmsArray := thmsArray.push (← simpExt.getTheorems)
            if let some simprocExt := simprocExt? then
              simprocs := simprocs.push (← simprocExt.getSimprocs)
          | .star => pure ()
          | .none => pure ()

        let mut ctx := ctx.setZetaDeltaSet zetaDeltaSet (← getZetaDeltaFVarIds)
        ctx := ctx.setSimpTheorems (thmsArray.set! 0 thms)
        if !ignoreStarArg && starArg then
          ctx ← applyStarArg ctx

        return { ctx, simprocs, simpArgs := args}
    -- If recovery is disabled, then we want simp argument elaboration failures to be exceptions.
    -- This affects `addSimpTheorem`.
    if (← read).recover then
      go
    else
      Term.withoutErrToSorry go
where
  /-- If `zetaDelta := false`, create a `FVarId` set with all local let declarations in the `simp` argument list. -/
  toZetaDeltaSet (stx : Syntax) (ctx : Simp.Context) : TacticM FVarIdSet := do
    if ctx.config.zetaDelta then return {}
    Term.withoutCheckDeprecated do -- We do not want to report deprecated constants in the first pass
      let mut s : FVarIdSet := {}
      for arg in stx[1].getSepArgs do
        if arg.getKind == ``Lean.Parser.Tactic.simpLemma then
          if arg[0].isNone && arg[1].isNone then
            let term := arg[2]
            let .expr (.fvar fvarId) ← resolveSimpIdTheorem? term | pure ()
            if (← fvarId.getDecl).isLet then
              s := s.insert fvarId
      return s

/-- Position for the `[..]` child syntax in the `simp` tactic. -/
def simpParamsPos := 4

/-- Position for the `only` child syntax in the `simp` tactic. -/
def simpOnlyPos := 3

def isSimpOnly (stx : TSyntax `tactic) : Bool :=
  stx.raw.getKind == ``Parser.Tactic.simp && !stx.raw[simpOnlyPos].isNone

def getSimpParams (stx : TSyntax `tactic) : Array Syntax :=
  stx.raw[simpParamsPos][1].getSepArgs

def setSimpParams (stx : TSyntax `tactic) (params : Array Syntax) : TSyntax `tactic :=
  if params.isEmpty then
    ⟨stx.raw.setArg simpParamsPos (mkNullNode)⟩
  else
    let paramsStx := #[mkAtom "[", (mkAtom ",").mkSep params, mkAtom "]"]
    ⟨stx.raw.setArg simpParamsPos (mkNullNode paramsStx)⟩

@[inline] def simpOnlyBuiltins : List Name := [``eq_self, ``iff_self]

structure MkSimpContextResult where
  ctx              : Simp.Context
  simprocs         : Simp.SimprocsArray
  dischargeWrapper : Simp.DischargeWrapper
  /-- The elaborated simp arguments with syntax -/
  simpArgs         : Array (Syntax × ElabSimpArgResult) := #[]

/--
   Create the `Simp.Context` for the `simp`, `dsimp`, and `simp_all` tactics.
   If `kind != SimpKind.simp`, the `discharge` option must be `none`

   TODO: generate error message if non `rfl` theorems are provided as arguments to `dsimp`.

   The argument `simpTheorems` defaults to `getSimpTheorems`,
   but allows overriding with an arbitrary mechanism to choose
   the simp theorems besides those specified in the syntax.
   Note that if the syntax includes `simp only`, the `simpTheorems` argument is ignored.
-/
def mkSimpContext (stx : Syntax) (eraseLocal : Bool) (kind := SimpKind.simp)
    (ignoreStarArg : Bool := false) (simpTheorems : CoreM SimpTheorems := getSimpTheorems) :
    TacticM MkSimpContextResult := do
  if !stx[2].isNone then
    if kind == SimpKind.simpAll then
      throwError "'simp_all' tactic does not support 'discharger' option"
    if kind == SimpKind.dsimp then
      throwError "'dsimp' tactic does not support 'discharger' option"
  let dischargeWrapper ← mkDischargeWrapper stx[2]
  let simpOnly := !stx[simpOnlyPos].isNone
  let simpTheorems ← if simpOnly then
    simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  else
    simpTheorems
  let simprocs ← if simpOnly then pure {} else Simp.getSimprocs
  let congrTheorems ← getSimpCongrTheorems
  let ctx ← Simp.mkContext
     (config := (← elabSimpConfig stx[1] (kind := kind)))
     (simpTheorems := #[simpTheorems])
     congrTheorems
  let r ← elabSimpArgs stx[4] (eraseLocal := eraseLocal) (kind := kind) (simprocs := #[simprocs]) (ignoreStarArg := ignoreStarArg) ctx
  return { r with dischargeWrapper }

/--
Runs the given action.
If it throws a maxRecDepth exception (nested or not), run the loop checking.
If it does not throw, run the loop checking only if explicitly enabled.
-/
@[inline] def withLoopChecking [Monad m] [MonadExcept Exception m] [MonadRuntimeException m] [MonadLiftT MetaM m]
    (r : MkSimpContextResult) (k : m α) : m α := do
  -- We use tryCatchRuntimeEx here, normal try-catch would swallow the trace messages
  -- from diagnostics
  let x ← tryCatchRuntimeEx do
      k
    fun e => do
      if e.isMaxRecDepth || e.toMessageData.hasTag (· = `nested.runtime.maxRecDepth) then
        go (force := true)
      throw e
  go (force := false)
  pure x
where
  go force : m Unit := liftMetaM do
    let { ctx, simprocs, dischargeWrapper := _, simpArgs } := r
    for (ref, arg) in simpArgs do
      for thm in arg.simpTheorems do
        withRef ref do
          Simp.checkLoops (force := force) ctx (methods := Simp.mkDefaultMethodsCore simprocs) thm

register_builtin_option tactic.simp.trace : Bool := {
  defValue := false
  descr    := "When tracing is enabled, calls to `simp` or `dsimp` will print an equivalent `simp only` call."
}

/--
If `stx` is the syntax of a `simp`, `simp_all` or `dsimp` tactic invocation, and
`usedSimps` is the set of simp lemmas used by this invocation, then `mkSimpOnly`
creates the syntax of an equivalent `simp only`, `simp_all only` or `dsimp only`
invocation.
-/
def mkSimpOnly (stx : Syntax) (usedSimps : Simp.UsedSimps) : MetaM Syntax := do
  let isSimpAll := stx.isOfKind ``Parser.Tactic.simpAll
  let mut stx := stx
  if stx[3].isNone then
    stx := stx.setArg 3 (mkNullNode #[mkAtom "only"])
  let mut args := #[]
  let mut localsOrStar := some #[]
  let lctx ← getLCtx
  let env ← getEnv
  for thm in usedSimps.toArray do
    match thm with
    | .decl declName post inv => -- global definitions in the environment
      if env.contains declName
         && (inv || !simpOnlyBuiltins.contains declName)
         && !Match.isMatchEqnTheorem env declName then
        let decl : Term ← `($(mkIdent (← unresolveNameGlobalAvoidingLocals declName)):ident)
        let arg ← match post, inv with
          | true,  true  => `(Parser.Tactic.simpLemma| ← $decl:term)
          | true,  false => `(Parser.Tactic.simpLemma| $decl:term)
          | false, true  => `(Parser.Tactic.simpLemma| ↓ ← $decl:term)
          | false, false => `(Parser.Tactic.simpLemma| ↓ $decl:term)
        args := args.push arg
      else if (← Simp.isBuiltinSimproc declName) then
        let decl := mkIdent declName
        let arg ← match post with
          | true  => `(Parser.Tactic.simpLemma| $decl:term)
          | false => `(Parser.Tactic.simpLemma| ↓ $decl:term)
        args := args.push arg
    | .fvar fvarId =>
      -- local hypotheses in the context
      if let some ldecl := lctx.find? fvarId then
        -- `simp_all` always uses all propositional hypotheses.
        -- So `simp_all only [x]`, only makes sense if `ldecl` is a let-variable.
        if isSimpAll && !ldecl.hasValue then
          continue
        localsOrStar := localsOrStar.bind fun locals =>
          if !ldecl.userName.isInaccessibleUserName && !ldecl.userName.hasMacroScopes &&
              (lctx.findFromUserName? ldecl.userName).get!.fvarId == ldecl.fvarId then
            some (locals.push ldecl.userName)
          else
            none
      -- Note: the `if let` can fail for `simp (config := {contextual := true})` when
      -- rewriting with a variable that was introduced in a scope. In that case we just ignore.
    | .stx _ thmStx => -- simp theorems provided in the local invocation
      args := args.push thmStx
    | .other _ => -- Ignore "special" simp lemmas such as constructed by `simp_all`.
      pure ()     -- We can't display them anyway.
  if let some locals := localsOrStar then
    args := args ++ (← locals.mapM fun id => `(Parser.Tactic.simpLemma| $(mkIdent id):ident))
  else
    args := args.push (← `(Parser.Tactic.simpStar| *))
  return setSimpParams stx args

def traceSimpCall (stx : Syntax) (usedSimps : Simp.UsedSimps) : MetaM Unit := do
  logInfoAt stx[0] m!"Try this: {← mkSimpOnly stx usedSimps}"


register_builtin_option linter.unusedSimpArgs : Bool := {
  defValue := true,
  descr := "enable the linter that warns when explicit `simp` arguments are unused.\n\
    \n\
    The linter suggests removing the unused arguments. This hint may not be correct in the case \
    that `simp [← thm]` is given, when `thm` has the `@[simp]` attribute, and it is relevant that \
    `thm` it disabled (which is a side-effect of specifying `← thm`). In that case, replace \
    it with `simp [- thm]`.\n\
    \n\
    When one `simp` invocation is run multiple times (e.g. `all_goals simp [thm]`), it warns \
    about simp arguments that are unused in all invocations. For this reason, the linter \
    does not warn about uses of `simp` inside a macro, as there it is usually not possible to see \
    all invocations."
}

structure UnusedSimpArgsInfo where
  mask : Array Bool
deriving TypeName

def pushUnusedSimpArgsInfo [Monad m] [MonadInfoTree m] (simpStx : Syntax) (mask : Array Bool) : m Unit := do
  pushInfoLeaf <| .ofCustomInfo {
    stx := simpStx
    value := .mk { mask := mask : UnusedSimpArgsInfo } }

/--
Checks the simp arguments for unused ones, and stores a bitmask of unused ones in the info tree,
to be picked up by the linter.
(This indirection is necessary because the same `simp` syntax may be executed multiple times,
and different simp arguments may be used in each step.)
-/
def warnUnusedSimpArgs (simpArgs : Array (Syntax × ElabSimpArgResult)) (usedSimps : Simp.UsedSimps) : MetaM Unit := do
  if simpArgs.isEmpty then return
  let mut mask : Array Bool := #[]
  for h : i in [:simpArgs.size] do
    let (ref, arg) := simpArgs[i]
    let used ←
      match arg with
      | .addEntries entries =>
        entries.anyM fun
          | .thm thm => return usedSimps.contains (← usedThmIdOfSimpTheorem thm)
          | .toUnfold declName => return usedSimps.contains (.decl declName)
          | .toUnfoldThms _declName thms => return thms.any (usedSimps.contains <| .decl ·)
      | .addSimproc declName post =>
        pure <| usedSimps.contains (.decl declName post)
      | .addLetToUnfold fvarId =>
        pure <| usedSimps.contains (.fvar fvarId)
      | .erase _
      | .eraseSimproc _
      | .ext _ _ _
      | .star
      | .none
      => pure true -- not supported yet
    mask := mask.push used
  pushUnusedSimpArgsInfo (← getRef) mask
where
  /--
  For equational theorems, usedTheorems record the declaration name. So if the user
  specified `foo.eq_1`, we get `foo` in `usedTheores`, but we still want to mark
  `foo.eq_1` as used.
  (cf. `recordSimpTheorem`)
  This may lead to unused, explicitly given `foo.eq_1` to not be warned about. Ok for now,
  eventually `recordSimpTheorem` could record the actual theorem, and the logic for
  treating `foo.eq_1` as `foo` be moved to `SimpTrace.lean`
  -/
  usedThmIdOfSimpTheorem (thm : SimpTheorem) : MetaM Origin := do
    let thmId := thm.origin
    if let .decl declName post false := thmId then
      if let some declName ← isEqnThm? declName then
        return (Origin.decl declName post false)
    return thmId


/--
`simpLocation ctx discharge? varIdToLemmaId loc`
runs the simplifier at locations specified by `loc`,
using the simp theorems collected in `ctx`
optionally running a discharger specified in `discharge?` on generated subgoals.

Its primary use is as the implementation of the
`simp [...] at ...` and `simp only [...] at ...` syntaxes,
but can also be used by other tactics when a `Syntax` is not available.

For many tactics other than the simplifier,
one should use the `withLocation` tactic combinator
when working with a `location`.
-/
def simpLocation (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) (discharge? : Option Simp.Discharge := none) (loc : Location) : TacticM Simp.Stats := do
  match loc with
  | Location.targets hyps simplifyTarget =>
    withMainContext do
      let fvarIds ← getFVarIds hyps
      go fvarIds simplifyTarget
  | Location.wildcard =>
    withMainContext do
      go (← (← getMainGoal).getNondepPropHyps) (simplifyTarget := true)
where
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM Simp.Stats := do
    let mvarId ← getMainGoal
    let (result?, stats) ← simpGoal mvarId ctx (simprocs := simprocs) (simplifyTarget := simplifyTarget) (discharge? := discharge?) (fvarIdsToSimp := fvarIdsToSimp)
    match result? with
    | none => replaceMainGoal []
    | some (_, mvarId) => replaceMainGoal [mvarId]
    return stats

def withSimpDiagnostics (x : TacticM Simp.Diagnostics) : TacticM Unit := do
  let stats ← x
  Simp.reportDiag stats

/-
  "simp" optConfig (discharger)? (" only")? (" [" ((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  (location)?
-/
@[builtin_tactic Lean.Parser.Tactic.simp] def evalSimp : Tactic := fun stx => withMainContext do withSimpDiagnostics do
  let r@{ ctx, simprocs, dischargeWrapper, simpArgs } ← mkSimpContext stx (eraseLocal := false)
  let stats ← dischargeWrapper.with fun discharge? =>
    withLoopChecking r do
      simpLocation ctx simprocs discharge? (expandOptLocation stx[5])
  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx stats.usedTheorems
  else if linter.unusedSimpArgs.get (← getOptions) then
    withRef stx do
      warnUnusedSimpArgs simpArgs stats.usedTheorems
  return stats.diag

@[builtin_tactic Lean.Parser.Tactic.simpAll] def evalSimpAll : Tactic := fun stx => withMainContext do withSimpDiagnostics do
  let r@{ ctx, simprocs, dischargeWrapper := _, simpArgs } ← mkSimpContext stx (eraseLocal := true) (kind := .simpAll) (ignoreStarArg := true)
  let (result?, stats) ←
    withLoopChecking r do
      simpAll (← getMainGoal) ctx (simprocs := simprocs)
  match result? with
  | none => replaceMainGoal []
  | some mvarId => replaceMainGoal [mvarId]
  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx stats.usedTheorems
  else if linter.unusedSimpArgs.get (← getOptions) then
    withRef stx do
      warnUnusedSimpArgs simpArgs stats.usedTheorems
  return stats.diag

def dsimpLocation (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) (loc : Location) : TacticM Unit := do
  match loc with
  | Location.targets hyps simplifyTarget =>
    withMainContext do
      let fvarIds ← getFVarIds hyps
      go fvarIds simplifyTarget
  | Location.wildcard =>
    withMainContext do
      go (← (← getMainGoal).getNondepPropHyps) (simplifyTarget := true)
where
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM Unit := withSimpDiagnostics do
    let mvarId ← getMainGoal
    let (result?, stats) ← dsimpGoal mvarId ctx simprocs (simplifyTarget := simplifyTarget) (fvarIdsToSimp := fvarIdsToSimp)
    match result? with
    | none => replaceMainGoal []
    | some mvarId => replaceMainGoal [mvarId]
    if tactic.simp.trace.get (← getOptions) then
      mvarId.withContext <| traceSimpCall (← getRef) stats.usedTheorems
    return stats.diag

@[builtin_tactic Lean.Parser.Tactic.dsimp] def evalDSimp : Tactic := fun stx => do
  let { ctx, simprocs, .. } ← withMainContext <| mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
  dsimpLocation ctx simprocs (expandOptLocation stx[5])

end Lean.Elab.Tactic

/-!
The following parsers for `simp` arguments are not actually used at present in the
implementation of `simp` above, but are useful for further tactics which need
to parse `simp` arguments.
-/
namespace Lean.Parser.Tactic

/-- Extract the arguments from a `simpArgs` syntax as an array of syntaxes -/
def getSimpArgs? : Syntax → Option (Array Syntax)
  | `(simpArgs| [$args,*]) => pure args.getElems
  | _ => none

/-- Extract the arguments from a `dsimpArgs` syntax as an array of syntaxes -/
def getDSimpArgs? : Syntax → Option (Array Syntax)
  | `(dsimpArgs| [$args,*]) => pure args.getElems
  | _                       => none

end Lean.Parser.Tactic
