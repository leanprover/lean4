/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.CoreM
import Lean.Namespace

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

@[deprecated "use `Lean.addDecl` instead to ensure new namespaces are registered" (since := "2024-12-03")]
def Environment.addDecl (env : Environment) (opts : Options) (decl : Declaration)
    (cancelTk? : Option IO.CancelToken := none) : Except Kernel.Exception Environment :=
  Environment.addDeclAux env opts decl cancelTk?

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

def addDecl (decl : Declaration) : CoreM Unit := do
  -- register namespaces for newly added constants; this used to be done by the kernel itself
  -- but that is incompatible with moving it to a separate task
  -- NOTE: we do not use `getTopLevelNames` here so that inductive types are registered as
  -- namespaces
  modifyEnv (decl.getNames.foldl registerNamePrefixes)

  if !Elab.async.get (← getOptions) then
    return (← doAdd)

  -- convert `Declaration` to `ConstantInfo` to use as a preliminary value in the environment until
  -- kernel checking has finished; not all cases are supported yet
  let (name, info, kind) ← match decl with
    | .thmDecl thm => pure (thm.name, .thmInfo thm, .thm)
    | .defnDecl defn => pure (defn.name, .defnInfo defn, .defn)
    | .mutualDefnDecl [defn] => pure (defn.name, .defnInfo defn, .defn)
    | .axiomDecl ax => pure (ax.name, .axiomInfo ax, .axiom)
    | _ => return (← doAdd)

  let env ← getEnv
  -- no environment extension changes to report after kernel checking; ensures we do not
  -- accidentally wait for this snapshot when querying extension states
  let async ← env.addConstAsync (reportExts := false) name kind
  -- report preliminary constant info immediately
  async.commitConst async.asyncEnv (some info)
  setEnv async.mainEnv
  let cancelTk ← IO.CancelToken.new
  let checkAct ← Core.wrapAsyncAsSnapshot (cancelTk? := cancelTk) fun _ => do
    setEnv async.asyncEnv
    try
      doAdd
    finally
      async.commitCheckEnv (← getEnv)
  let t ← BaseIO.mapTask checkAct env.checked
  let endRange? := (← getRef).getTailPos?.map fun pos => ⟨pos, pos⟩
  Core.logSnapshotTask { stx? := none, reportingRange? := endRange?, task := t, cancelTk? := cancelTk }
where
  doAdd := do
    profileitM Exception "type checking" (← getOptions) do
      withTraceNode `Kernel (fun _ => return m!"typechecking declarations {decl.getTopLevelNames}") do
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


def addAndCompile (decl : Declaration) : CoreM Unit := do
  addDecl decl
  compileDecl decl

end Lean
