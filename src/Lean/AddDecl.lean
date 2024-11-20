/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.CoreM
import Lean.Language.Basic
import Lean.Elab.Exception

namespace Lean

@[deprecated "use `Lean.addAndCompile` instead"]
def Environment.addAndCompile (env : Environment) (opts : Options) (decl : Declaration)
    (cancelTk? : Option IO.CancelToken := none) : Except Kernel.Exception Environment := do
  let env ← addDecl env opts decl cancelTk?
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
  | .str p _ => if isNamespaceName p then go (Environment.registerNamespace env p) p else env
  | _        => env

def addDecl (decl : Declaration) : CoreM Unit := do
  if true then
    let preEnv ← getEnv
    let (name, info, kind) ← match decl with
      | .thmDecl thm => pure (thm.name, .thmInfo thm, .thm)
      | .defnDecl defn => pure (defn.name, .defnInfo defn, .defn)
      | .mutualDefnDecl [defn] => pure (defn.name, .defnInfo defn, .defn)
      | .axiomDecl ax => pure (ax.name, .axiomInfo ax, .axiom)
      | .inductDecl _ _ types _ =>
        -- used to be triggered by adding `X.recOn` etc. to the environment but that's async now
        modifyEnv (types.foldl (registerNamePrefixes · <| ·.name ++ `rec));
        doAdd
        return
      | _ => return (← doAdd)
    let async ← preEnv.addConstAsync (reportExts := false) name kind
    async.commitConst async.asyncEnv (some info)
    setEnv async.mainEnv
    let ctx ← read
    let checkAct ← Core.wrapAsyncAsSnapshot fun _ => do
      try
        setEnv async.asyncEnv
        doAdd
        async.checkAndCommitEnv (← getEnv) ctx.options ctx.cancelTk?
      finally
        async.commitFailure
    let _ ← BaseIO.mapTask (fun _ => checkAct) preEnv.checked
    return
  doAdd
where doAdd := do
  profileitM Exception "type checking" (← getOptions) do
    withTraceNode `Kernel (fun _ => return m!"typechecking declaration") do
      if !(← MonadLog.hasErrors) && decl.hasSorry then
        logWarning "declaration uses 'sorry'"
      match (← getEnv).addDecl (← getOptions) decl (← read).cancelTk? with
      | .ok    env => setEnv (← decl.getNames.foldlM (m := BaseIO) (·.enableRealizationsForConst) env)
      | .error ex  => throwKernelException ex

def addAndCompile (decl : Declaration) : CoreM Unit := do
  addDecl decl
  compileDecl decl

end Lean
