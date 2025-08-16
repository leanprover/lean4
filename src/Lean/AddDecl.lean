/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.CoreM
public import Lean.Namespace
public import Lean.Util.CollectAxioms

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



private def isNamespaceName : Name → Bool
  | .str .anonymous _ => true
  | .str p _          => isNamespaceName p
  | _                 => false

private def registerNamePrefixes (env : Environment) (name : Name) : Environment :=
  match name with
    | .str _ s =>
      if s.get 0 == '_' then
        -- Do not register namespaces that only contain internal declarations.
        env
      else
        go env name
    | _ => env
where go env
  | .str p _ => if isNamespaceName p then go (env.registerNamespace p) p else env
  | _        => env

private builtin_initialize privateConstKindsExt : MapDeclarationExtension ConstantKind ←
  -- Use `sync` so we can add entries from anywhere without restrictions
  mkMapDeclarationExtension (asyncMode := .sync)

/--
Returns the kind of the declaration as originally declared instead of as exported. This information
is stored by `Lean.addDecl` and may be inaccurate if that function was circumvented. Returns `none`
if the declaration was not found.
-/
def getOriginalConstKind? (env : Environment) (declName : Name) : Option ConstantKind := do
  -- Use `local` as for asynchronous decls from the current module, `findAsync?` below will yield
  -- the same result but potentially earlier (after `addConstAsync` instead of `addDecl`)
  privateConstKindsExt.find? (asyncMode := .local) env declName <|>
    (env.setExporting false |>.findAsync? declName).map (·.kind)

/--
Checks whether the declaration was originally declared as a theorem; see also
`Lean.getOriginalConstKind?`. Returns `false` if the declaration was not found.
-/
def wasOriginallyTheorem (env : Environment) (declName : Name) : Bool :=
  getOriginalConstKind? env declName |>.map (· matches .thm) |>.getD false

def addDecl (decl : Declaration) : CoreM Unit := do
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
      if (← getEnv).header.isModule then
        exportedInfo? := some <| .axiomInfo { thm with isUnsafe := false }
      pure (thm.name, .thmInfo thm, .thm)
    | .defnDecl defn | .mutualDefnDecl [defn] =>
      if (← getEnv).header.isModule && !(← getEnv).isExporting then
        exportedInfo? := some <| .axiomInfo { defn with isUnsafe := defn.safety == .unsafe }
      pure (defn.name, .defnInfo defn, .defn)
    | .axiomDecl ax => pure (ax.name, .axiomInfo ax, .axiom)
    | _ => return (← doAdd)

  if decl.getTopLevelNames.all isPrivateName then
    exportedInfo? := none
  else
    -- preserve original constant kind in extension if different from exported one
    if exportedInfo?.isSome then
      modifyEnv (privateConstKindsExt.insert · name kind)
    else
      exportedInfo? := some info

  -- no environment extension changes to report after kernel checking; ensures we do not
  -- accidentally wait for this snapshot when querying extension states
  let env ← getEnv
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
      withTraceNode `Kernel (return m!"{exceptEmoji ·} typechecking declarations {decl.getTopLevelNames}") do
        if warn.sorry.get (← getOptions) then
          if !(← MonadLog.hasErrors) && decl.hasSorry then
            logWarning <| .tagged `hasSorry m!"declaration uses 'sorry'"
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


def addAndCompile (decl : Declaration) (logCompileErrors : Bool := true) : CoreM Unit := do
  addDecl decl
  compileDecl decl (logErrors := logCompileErrors)

end Lean
