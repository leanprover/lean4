/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Sorry
public import Lean.Util.CollectAxioms
public import Lean.OriginalConstKind
public import Lean.AutoDecl
import Lean.Linter.Init
import Lean.Compiler.MetaAttr
import Lean.Meta.Check
import Lean.Meta.Instances
import Lean.ReducibilityAttrs
import all Lean.OriginalConstKind

public section

namespace Lean

/-- Adds given declaration to the environment, respecting `debug.skipKernelTC`. -/
def Kernel.Environment.addDecl (env : Environment) (opts : Options) (decl : Declaration)
    (cancelTk? : Option IO.CancelToken := none) : Except Exception Environment :=
  if debug.skipKernelTC.get opts then
    addDeclWithoutChecking env decl
  else
    addDeclCore env (Core.getMaxHeartbeats opts).toUSize decl cancelTk?

private def Environment.addDeclAux (env : Environment) (opts : Options) (decl : Declaration)
    (cancelTk? : Option IO.CancelToken := none) : Except Kernel.Exception Environment :=
  env.addDeclCore (Core.getMaxHeartbeats opts).toUSize decl cancelTk? (!debug.skipKernelTC.get opts)

open Linter in
/--
Saves the state of `Lean.Option`s associated with environment linters into `envLinterSnapshotExt`
-/
def snapshotEnvLinterOptions (declName : Name) : CoreM Unit := do
  let envLinterOpts ← envLinterOptionsRef.get
  unless envLinterOpts.isEmpty do
    let linterOptions ← getLinterOptions
    unless ← isAutoDeclOrPrivate_Internal declName do
      let mut snapshot : NameMap Bool := {}
      for opt in envLinterOpts do
        snapshot := snapshot.insert opt.name (getLinterValue opt linterOptions)
      modifyEnv (envLinterSnapshotExt.insert · declName snapshot)

private def isNamespaceName : Name → Bool
  | .str .anonymous _ => true
  | .str p _          => isNamespaceName p
  | _                 => false

private def registerNamePrefixes (env : Environment) (name : Name) : Environment :=
  -- namespaces are based on the un-encoded name (`isNamespaceName` is false for any private name)
  let name := privateToUserName name
  match name with
    | .str _ s =>
      if s.front == '_' then
        -- Do not register namespaces that only contain internal declarations.
        env
      else
        go env name
    | _ => env
where go env
  | .str p _ => if isNamespaceName p then go (env.registerNamespace p) p else env
  | _        => env

/-- If `warn.sorry` is set to true, then, so long as the message log does not already have any errors,
declarations with `sorryAx` generate the "declaration uses `sorry`" warning. -/
register_builtin_option warn.sorry : Bool := {
  defValue := true
  descr    := "warn about uses of `sorry` in declarations added to the environment"
}

/--
If the `warn.sorry` option is set to true and there are no errors in the log already,
logs a warning if the declaration uses `sorry`.
-/
def warnIfUsesSorry (decl : Declaration) : CoreM Unit := do
  if warn.sorry.get (← getOptions) then
    if !(← MonadLog.hasErrors) && decl.hasSorry then
      -- Find an actual sorry expression to use for `sorry`.
      -- That way the user can hover over it to see its type and use "go to definition" if it is a labeled sorry.
      let findSorry : StateRefT (Array (Bool × MessageData)) MetaM Unit := decl.forEachSorryM fun s => do
        let s' ← addMessageContext s
        modify fun arr => arr.push (s.isSyntheticSorry, s')
      let (_, sorries) ← findSorry |>.run #[] |>.run'
      -- Prefer reporting a synthetic sorry.
      -- These can appear without logged errors if `decl` is referring to declarations with elaboration errors;
      -- that's where a user should direct their focus.
      if let some (_, s) := sorries.find? (·.1) <|> sorries[0]? then
        logWarning <| .tagged `hasSorry m!"declaration uses `{s}`"
      else
        -- This case should not happen, but it ensures a warning will get logged no matter what.
        logWarning <| .tagged `hasSorry m!"declaration uses `sorry`"

/--
If `linter.checkDeclsAtImplicit` is set to true, declarations whose type is type-correct at
`.default` transparency but not at `.implicit` transparency generate a warning suggesting
definitions that could be marked `@[implicit_reducible]`.
-/
register_builtin_option linter.checkDeclsAtImplicit : Bool := {
  defValue := false
  descr    := "warn when a declaration's type is not type-correct at `.implicit` transparency"
}

/--
The top-level `(name, type)` pairs whose types `warnIfDeclIllTypedAtImplicit` checks:
definitions, theorems, opaque constants, and axioms. Inductives are skipped for now.
-/
private def declTypesToCheck : Declaration → Array (Name × Expr)
  | .axiomDecl v       => #[(v.name, v.type)]
  | .defnDecl v        => #[(v.name, v.type)]
  | .thmDecl v         => #[(v.name, v.type)]
  | .opaqueDecl v      => #[(v.name, v.type)]
  | .mutualDefnDecl vs => (vs.map fun v => (v.name, v.type)).toArray
  | .inductDecl ..     => #[]
  | .quotDecl          => #[]

/--
Returns the semireducible non-instance definitions that `Meta.check declType .default`
unfolds but the `.implicit` check does not, or `none` if `declType` is already type-correct at
`.implicit` transparency (or is not even type-correct at `.default`). Mirrors the inner loop of
`Lean.Linter.tacticCheckInstances`.

Runs under `Core.withCurrHeartbeats` and returns `none` in case of heartbeat exhaustion. this
diagnostic must never abort the surrounding elaboration, nor draw on a tactic's already-spent
heartbeat budget. Interrupt exceptions are re-raised, never swallowed.
-/
private def checkTypeAtImplicitTransparency (declType : Expr) : MetaM (Option (Array Name)) :=
  Core.withCurrHeartbeats do
  -- Fast path: Check the type at `.implicit`, without `diagnostics true`. Failure should be the
  -- absolute exception, so we optimize for the frequent case.
  let implicitFailed : Bool ←
    try
      Meta.check declType .implicit
      pure false
    catch e =>
      if e.isInterrupt then throw e
      else if e.isRuntime then
        logWarning m!"The `checkDeclsAtImplicit` linter failed with an unexpected error while checking the type of `{declType}` at implicit transparency.\n{e.toMessageData}"
        return none
      else pure true
  unless implicitFailed do return none
  let origDiag := (← get).diag
  let result : Option (Array Name) ← withOptions (diagnostics.set · true) do
    -- A type that is not even correct at `.default` is a more fundamental problem; ignore it here.
    try Meta.check declType .default
    catch e =>
      if e.isInterrupt then
        modify ({ · with diag := origDiag })
        throw e
      else
        -- Any error while checking the type at default transparency is an unexpected error.
        logWarning m!"The `checkDeclsAtImplicit` linter failed with an unexpected error while checking the type of `{declType}` at default transparency.\n{e.toMessageData}"
        return none
    let counterDefault := (← get).diag.unfoldCounter
    -- Reset the unfold counter and re-check at `.implicit` to record what it unfolds.
    modify ({ · with diag := origDiag })
    try Meta.check declType .implicit
    catch e =>
      if e.isInterrupt then
        modify ({ · with diag := origDiag })
        throw e
      else if e.isRuntime then
        -- Warn if a resource limit has been reached.
        logWarning m!"The `checkDeclsAtImplicit` linter failed with an unexpected error while checking the type of `{declType}` at implicit transparency.\n{e.toMessageData}"
        return none
      else
        -- This check is expected to fail, so nothing to do in this case.
        -- The `else` branch only exists for clarity.
        pure ()
    let counterImplicit := (← get).diag.unfoldCounter
    let env ← getEnv
    -- Definitions unfolded by the `.default` check but not the `.implicit` one are the
    -- candidates for `@[implicit_reducible]`. Only consider semireducible non-instances.
    let mut candidates : Array Name := #[]
    for (n, countDefault) in counterDefault do
      let countImplicit := counterImplicit.find? n |>.getD 0
      if countDefault > countImplicit
          && getReducibilityStatusCore env n matches .semireducible
          && !Meta.isInstanceCore env n then
        candidates := candidates.push n
    return some candidates
  -- Always restore the original diagnostics snapshot.
  modify ({ · with diag := origDiag })
  return result

/--
If `linter.checkDeclsAtImplicit` is enabled, warns when a declaration's type is type-correct at
`.default` transparency but not at `.implicit` transparency, suggesting semireducible
constants that could be be marked `@[implicit_reducible]` to fix the mismatch.
-/
def warnIfDeclIllTypedAtImplicit (decl : Declaration) : CoreM Unit := do
  unless linter.checkDeclsAtImplicit.get (← getOptions) do return
  -- Stay quiet on declarations that already produced errors.
  if ← MonadLog.hasErrors then return
  for (declName, declType) in declTypesToCheck decl do
    -- Compiler-internal auto-declarations (equation lemmas, etc.) would be noisy; skip them.
    if ← isAutoDeclOrPrivate_Internal declName then continue
    let some candidates ← (checkTypeAtImplicitTransparency declType).run' | continue
    if candidates.isEmpty then continue
    let bullets := MessageData.joinSep
      (candidates.toList.map (m!"{MessageData.ofConstName ·}")) Format.line
    Linter.logLint linter.checkDeclsAtImplicit (← getRef)
      m!"declaration {MessageData.ofConstName declName} is not type-correct at \
        `.implicit` transparency; consider marking some of the following as \
        `@[implicit_reducible]`:{indentD bullets}"

builtin_initialize
  registerTraceClass `addDecl

private def addDeclCore (decl : Declaration) (forceExpose : Bool) : CoreM Unit :=
  withTraceNode `addDecl (fun _ => return m!"adding declarations {decl.getNames}") do
  -- register namespaces for newly added constants; this used to be done by the kernel itself
  -- but that is incompatible with moving it to a separate task
  -- NOTE: we do not use `getTopLevelNames` here so that inductive types are registered as
  -- namespaces
  modifyEnv (decl.getNames.foldl registerNamePrefixes)

  -- convert `Declaration` to `ConstantInfo` to use as a preliminary value in the environment until
  -- kernel checking has finished; not all cases are supported yet
  let mut exportedInfo? := none
  let (name, info, kind) ← match decl with
    | .thmDecl thm =>
      if !forceExpose && (← getEnv).header.isModule then
        trace[addDecl] "exporting theorem {thm.name} as axiom"
        exportedInfo? := some <| .axiomInfo { thm with isUnsafe := false }
      pure (thm.name, .thmInfo thm, .thm)
    | .defnDecl defn | .mutualDefnDecl [defn] =>
      if !forceExpose && (← getEnv).header.isModule && !(← getEnv).isExporting then
        trace[addDecl] "exporting definition {defn.name} as axiom"
        exportedInfo? := some <| .axiomInfo { defn with isUnsafe := defn.safety == .unsafe }
      pure (defn.name, .defnInfo defn, .defn)
    | .opaqueDecl op =>
      if !forceExpose && (← getEnv).header.isModule && !(← getEnv).isExporting then
        trace[addDecl] "exporting opaque {op.name} as axiom"
        exportedInfo? := some <| .axiomInfo { op with }
      pure (op.name, .opaqueInfo op, .opaque)
    | .axiomDecl ax => pure (ax.name, .axiomInfo ax, .axiom)
    | _ =>
      trace[addDecl] "no matching async adding rules, adding synchronously"
      return (← doAdd)

  -- Check early so we can avoid related env ext panics that would happen before the check in the
  -- kernel.
  if (← getEnv).containsOnBranch name then
    throwKernelException <| .alreadyDeclared (← getEnv).toKernelEnv name

  if decl.getTopLevelNames.all isPrivateName then
    if (← ResolveName.backward.privateInPublic.getM) then
      trace[addDecl] "private decl under `privateInPublic`, exporting as is"
      exportedInfo? := some info
    else
      trace[addDecl] "not exporting private declaration at all"
      exportedInfo? := none
  else
    -- preserve original constant kind in extension if different from exported one
    if exportedInfo?.isSome then
      modifyEnv (privateConstKindsExt.insert · name kind)
    else
      trace[addDecl] "no matching exporting rules, exporting as is"
      exportedInfo? := some info

  let env ← getEnv
  -- no environment extension changes to report after kernel checking; ensures we do not
  -- accidentally wait for this snapshot when querying extension states
  let async ← env.addConstAsync (reportExts := false) name kind
    (exportedKind? := exportedInfo?.map (.ofConstantInfo))
  -- report preliminary constant info immediately
  async.commitConst async.asyncEnv (some info) (exportedInfo? <|> info)
  setEnv async.mainEnv

  let doAddAndCommit := do
    setEnv async.asyncEnv
    try
      doAdd
    finally
      async.commitCheckEnv (← getEnv)

  if Elab.async.get (← getOptions) then
    let cancelTk ← IO.CancelToken.new
    let checkAct ← Core.wrapAsyncAsSnapshot (cancelTk? := cancelTk) fun _ => doAddAndCommit
    let t ← BaseIO.mapTask checkAct env.checked
    -- Do not display reporting range; most uses of `addDecl` are for registering auxiliary decls
    -- users should not worry about and other callers can add a separate task with ranges
    -- themselves, see `MutualDef`.
    Core.logSnapshotTask { stx? := none, reportingRange := .skip, task := t, cancelTk? := cancelTk }
  else
    try
      doAddAndCommit
    finally
      setEnv async.mainEnv
where
  doAdd := do
    profileitM Exception "type checking" (← getOptions) do
      withTraceNode `Kernel (fun _ => return m!"typechecking declarations {decl.getTopLevelNames}") do
        warnIfUsesSorry decl
        warnIfDeclIllTypedAtImplicit decl
        try
          let env ← (← getEnv).addDeclAux (← getOptions) decl (← read).cancelTk?
            |> ofExceptKernelException
          setEnv env
        catch ex =>
          -- avoid follow-up errors by (trying to) add broken decl as axiom
          addAsAxiom
          throw ex
  addAsAxiom := do
    -- try to add as axiom with given type for def/theorem
    match decl with
    | .defnDecl d | .thmDecl d =>
      let fallbackDecl := .axiomDecl {
        name := d.name, levelParams := d.levelParams, type := d.type, isUnsafe := false
      }
      try
        let env ← (← getEnv).addDeclAux (← getOptions) fallbackDecl (← read).cancelTk?
          |> ofExceptKernelException
        setEnv env
        return
      catch _ => pure ()
    | _ => pure ()

    -- otherwise, add as axiom with type `sorry`
    for n in decl.getNames do
      let fallbackDecl := .axiomDecl {
        name := n, levelParams := []
        type := mkApp2 (mkConst ``sorryAx [1]) (mkSort 0) (mkConst ``true), isUnsafe := false
      }
      try
        let env ← (← getEnv).addDeclAux (← getOptions) fallbackDecl (← read).cancelTk?
          |> ofExceptKernelException
        setEnv env
        return
      catch _ => pure ()

/--
Adds the given declaration to the environment's private scope, deriving a suitable presentation in
the public scope if under the module system and if the declaration is not private. If `forceExpose`
is true, exposes the declaration body, i.e. preserves the full representation in the public scope,
independently of `Environment.isExporting` and even for theorems.
-/
def addDecl (decl : Declaration) (forceExpose := false) : CoreM Unit := do
  addDeclCore decl forceExpose
  discard <| decl.getTopLevelNames.mapM snapshotEnvLinterOptions

def addAndCompile (decl : Declaration) (logCompileErrors : Bool := true)
    (markMeta : Bool := false) : CoreM Unit := do
  addDecl decl
  if markMeta then
    for n in decl.getNames do
      modifyEnv (Lean.markMeta · n)
  compileDecl decl (logErrors := logCompileErrors)

end Lean
