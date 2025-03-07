/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp
import Lean.Meta.Tactic.Replace
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

private def addDeclToUnfoldOrTheorem (config : Meta.ConfigWithKey) (thms : SimpTheorems) (id : Origin) (e : Expr) (post : Bool) (inv : Bool) (kind : SimpKind) : MetaM SimpTheorems := do
  if e.isConst then
    let declName := e.constName!
    let info ← getConstInfo declName
    if (← isProp info.type) then
      thms.addConst declName (post := post) (inv := inv)
    else
      if inv then
        throwError "invalid '←' modifier, '{declName}' is a declaration name to be unfolded"
      if kind == .dsimp then
        return thms.addDeclToUnfoldCore declName
      else
        thms.addDeclToUnfold declName
  else if e.isFVar then
    let fvarId := e.fvarId!
    let decl ← fvarId.getDecl
    if (← isProp decl.type) then
      thms.add id #[] e (post := post) (inv := inv) (config := config)
    else if !decl.isLet then
      throwError "invalid argument, variable is not a proposition or let-declaration"
    else if inv then
      throwError "invalid '←' modifier, '{e}' is a let-declaration name to be unfolded"
    else
      return thms.addLetDeclToUnfold fvarId
  else
    thms.add id #[] e (post := post) (inv := inv) (config := config)

private def addSimpTheorem (config : Meta.ConfigWithKey) (thms : SimpTheorems) (id : Origin) (stx : Syntax) (post : Bool) (inv : Bool) : TermElabM SimpTheorems := do
  let thm? ← Term.withoutModifyingElabMetaStateWithInfo <| withRef stx do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    if e.hasSyntheticSorry then
      return none
    let e := e.eta
    if e.hasMVar then
      let r ← abstractMVars e
      return some (r.paramNames, r.expr)
    else
      return some (#[], e)
  if let some (levelParams, proof) := thm? then
    thms.add id levelParams proof (post := post) (inv := inv) (config := config)
  else
    return thms

structure ElabSimpArgsResult where
  ctx      : Simp.Context
  simprocs : Simp.SimprocsArray
  starArg  : Bool := false

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

/--
  Elaborate extra simp theorems provided to `simp`. `stx` is of the form `"[" simpTheorem,* "]"`
  If `eraseLocal == true`, then we consider local declarations when resolving names for erased theorems (`- id`),
  this option only makes sense for `simp_all` or `*` is used.
  When `recover := true`, try to recover from errors as much as possible so that users keep seeing
  the current goal.
-/
def elabSimpArgs (stx : Syntax) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) (eraseLocal : Bool) (kind : SimpKind) : TacticM ElabSimpArgsResult := do
  if stx.isNone then
    return { ctx, simprocs }
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
        let mut thmsArray := ctx.simpTheorems
        let mut thms      := thmsArray[0]!
        let mut simprocs  := simprocs
        let mut starArg   := false
        for arg in stx[1].getSepArgs do
          try -- like withLogging, but compatible with do-notation
            if arg.getKind == ``Lean.Parser.Tactic.simpErase then
              let fvar? ← if eraseLocal || starArg then Term.isLocalIdent? arg[1] else pure none
              if let some fvar := fvar? then
                -- We use `eraseCore` because the simp theorem for the hypothesis was not added yet
                thms := thms.eraseCore (.fvar fvar.fvarId!)
              else
                let id := arg[1]
                if let .ok declName ← observing (realizeGlobalConstNoOverloadWithInfo id) then
                  if (← Simp.isSimproc declName) then
                    simprocs := simprocs.erase declName
                  else if ctx.config.autoUnfold then
                    thms := thms.eraseCore (.decl declName)
                  else
                    thms ← withRef id <| thms.erase (.decl declName)
                else
                  -- If `id` could not be resolved, we should check whether it is a builtin simproc.
                  -- before returning error.
                  let name := id.getId.eraseMacroScopes
                  if (← Simp.isBuiltinSimproc name) then
                    simprocs := simprocs.erase name
                  else
                    withRef id <| throwUnknownConstant name
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
                thms ← addDeclToUnfoldOrTheorem ctx.indexConfig thms (.stx name arg) e post inv kind
              | .simproc declName =>
                simprocs ← simprocs.add declName post
              | .ext (some ext₁) (some ext₂) _ =>
                thmsArray := thmsArray.push (← ext₁.getTheorems)
                simprocs  := simprocs.push (← ext₂.getSimprocs)
              | .ext (some ext₁) none _ =>
                thmsArray := thmsArray.push (← ext₁.getTheorems)
              | .ext none (some ext₂) _ =>
                simprocs  := simprocs.push (← ext₂.getSimprocs)
              | .none    =>
                let name ← mkFreshId
                thms ← addSimpTheorem ctx.indexConfig thms (.stx name arg) term post inv
            else if arg.getKind == ``Lean.Parser.Tactic.simpStar then
              starArg := true
            else
              throwUnsupportedSyntax
          catch ex =>
            if (← read).recover then
              logException ex
            else
              throw ex
        let ctx := ctx.setZetaDeltaSet zetaDeltaSet (← getZetaDeltaFVarIds)
        return { ctx := ctx.setSimpTheorems (thmsArray.set! 0 thms), simprocs, starArg }
    -- If recovery is disabled, then we want simp argument elaboration failures to be exceptions.
    -- This affects `addSimpTheorem`.
    if (← read).recover then
      go
    else
      Term.withoutErrToSorry go
where
  isSimproc? (e : Expr) : MetaM (Option Name) := do
    let .const declName _ := e | return none
    unless (← Simp.isSimproc declName) do return none
    return some declName

  resolveSimpIdTheorem? (simpArgTerm : Term) : TacticM ResolveSimpIdResult := do
    let resolveExt (n : Name) : TacticM ResolveSimpIdResult := do
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
  let r ← elabSimpArgs stx[4] (eraseLocal := eraseLocal) (kind := kind) (simprocs := #[simprocs]) ctx
  if !r.starArg || ignoreStarArg then
    return { r with dischargeWrapper }
  else
    let ctx := r.ctx
    let simprocs := r.simprocs
    let mut simpTheorems := ctx.simpTheorems
    /-
    When using `zetaDelta := false`, we do not expand let-declarations when using `[*]`.
    Users must explicitly include it in the list.
    -/
    let hs ← getPropHyps
    for h in hs do
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr (config := ctx.indexConfig)
    let ctx := ctx.setSimpTheorems simpTheorems
    return { ctx, simprocs, dischargeWrapper }

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
  let { ctx, simprocs, dischargeWrapper } ← mkSimpContext stx (eraseLocal := false)
  let stats ← dischargeWrapper.with fun discharge? =>
    simpLocation ctx simprocs discharge? (expandOptLocation stx[5])
  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx stats.usedTheorems
  return stats.diag

@[builtin_tactic Lean.Parser.Tactic.simpAll] def evalSimpAll : Tactic := fun stx => withMainContext do withSimpDiagnostics do
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := true) (kind := .simpAll) (ignoreStarArg := true)
  let (result?, stats) ← simpAll (← getMainGoal) ctx (simprocs := simprocs)
  match result? with
  | none => replaceMainGoal []
  | some mvarId => replaceMainGoal [mvarId]
  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx stats.usedTheorems
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
