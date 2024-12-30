/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.CoreM

namespace Lean

register_builtin_option debug.skipKernelTC : Bool := {
  defValue := false
  group    := "debug"
  descr    := "skip kernel type checker. WARNING: setting this option to true may compromise soundness because your proofs will not be checked by the Lean kernel"
}

/-- Adds given declaration to the environment, respecting `debug.skipKernelTC`. -/
def Kernel.Environment.addDecl (env : Environment) (opts : Options) (decl : Declaration)
    (cancelTk? : Option IO.CancelToken := none) : Except Exception Environment :=
  if debug.skipKernelTC.get opts then
    addDeclWithoutChecking env decl
  else
    addDeclCore env (Core.getMaxHeartbeats opts).toUSize decl cancelTk?

private def Environment.addDeclAux (env : Environment) (opts : Options) (decl : Declaration)
    (cancelTk? : Option IO.CancelToken := none) : Except Kernel.Exception Environment :=
  if debug.skipKernelTC.get opts then
    addDeclWithoutChecking env decl
  else
    addDeclCore env (Core.getMaxHeartbeats opts).toUSize decl cancelTk?

@[deprecated "use `Lean.addDecl` instead to ensure new namespaces are registered" (since := "2024-12-03")]
def Environment.addDecl (env : Environment) (opts : Options) (decl : Declaration)
    (cancelTk? : Option IO.CancelToken := none) : Except Kernel.Exception Environment :=
  Environment.addDeclAux env opts decl cancelTk?

@[deprecated "use `Lean.addAndCompile`  instead to ensure new namespaces are registered" (since := "2024-12-03")]
def Environment.addAndCompile (env : Environment) (opts : Options) (decl : Declaration)
    (cancelTk? : Option IO.CancelToken := none) : Except Kernel.Exception Environment := do
  let env ← addDeclAux env opts decl cancelTk?
  compileDecl env opts decl

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
  let mut env ← getEnv
  -- register namespaces for newly added constants; this used to be done by the kernel itself
  -- but that is incompatible with moving it to a separate task
  env := decl.getNames.foldl registerNamePrefixes env
  if let .inductDecl _ _ types _ := decl then
    env := types.foldl (registerNamePrefixes · <| ·.name ++ `rec) env

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

  -- no environment extension changes to report after kernel checking; ensures we do not
  -- accidentally wait for this snapshot when querying extension states
  let async ← env.addConstAsync (reportExts := false) name kind
  -- report preliminary constant info immediately
  async.commitConst async.asyncEnv (some info)
  setEnv async.mainEnv
  let checkAct ← Core.wrapAsyncAsSnapshot fun _ => do
    try
      setEnv async.asyncEnv
      doAdd
      async.checkAndCommitEnv (← getEnv)
    finally
      async.commitFailure
  let t ← BaseIO.mapTask (fun _ => checkAct) env.checked
  let endRange? := (← getRef).getTailPos?.map fun pos => ⟨pos, pos⟩
  Core.logSnapshotTask { range? := endRange?, task := t }
where doAdd := do
  profileitM Exception "type checking" (← getOptions) do
    withTraceNode `Kernel (fun _ => return m!"typechecking declarations {decl.getNames}") do
      if !(← MonadLog.hasErrors) && decl.hasSorry then
        logWarning m!"declaration uses 'sorry'"
      let env ← (← getEnv).addDeclAux (← getOptions) decl (← read).cancelTk?
        |> ofExceptKernelException
      setEnv env

def addAndCompile (decl : Declaration) : CoreM Unit := do
  addDecl decl
  compileDecl decl

end Lean
