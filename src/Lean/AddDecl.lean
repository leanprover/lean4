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

private def addTraceAsMessagesCore [Monad m] [MonadRef m] [MonadLog m] [MonadTrace m] (log : MessageLog) : m MessageLog := do
  let traces ← getResetTraces
  if traces.isEmpty then return log
  let mut pos2traces : Std.HashMap (String.Pos × String.Pos) (Array MessageData) := ∅
  for traceElem in traces do
    let ref := replaceRef traceElem.ref (← getRef)
    let pos := ref.getPos?.getD 0
    let endPos := ref.getTailPos?.getD pos
    pos2traces := pos2traces.insert (pos, endPos) <| pos2traces.getD (pos, endPos) #[] |>.push traceElem.msg
  let mut log := log
  let traces' := pos2traces.toArray.qsort fun ((a, _), _) ((b, _), _) => a < b
  for ((pos, endPos), traceMsg) in traces' do
    let data := .tagged `_traceMsg <| .joinSep traceMsg.toList "\n"
    log := log.add <| Elab.mkMessageCore (← getFileName) (← getFileMap) data .information pos endPos
  return log

def addTraceAsMessages : CoreM Unit := do
  -- do not add trace messages if `trace.profiler.output` is set as it would be redundant and
  -- pretty printing the trace messages is expensive
  if trace.profiler.output.get? (← getOptions) |>.isNone then
    Core.setMessageLog (← addTraceAsMessagesCore (← Core.getMessageLog))

open Language in
/--
Wraps the given action for use in `BaseIO.asTask` etc., discarding its final state except for the
message log, which is reported in the returned snapshot.
-/
def runAsyncAsSnapshot (act : Unit → CoreM (Array (SnapshotTask SnapshotTree))) (desc := "") : CoreM (BaseIO SnapshotTree) := do
  let t ← runAsync do
   IO.FS.withIsolatedStreams (isolateStderr := stderrAsMessages.get (← getOptions)) do
    let tid ← IO.getLeanThreadID
    modifyTraceState fun _ => { tid }
    let trees ←
      try
        withTraceNode `Elab.async (fun _ => return desc) do
          act ()
      catch e =>
        logError e.toMessageData
        pure #[]
      finally
        addTraceAsMessages
    return (trees, (← Core.saveState))
  let ctx ← readThe Core.Context
  return do
    match (← t.toBaseIO) with
    | .ok (output, trees, st) =>
      let mut msgs := st.messages
      if !output.isEmpty then
        msgs := msgs.add {
          fileName := ctx.fileName
          severity := MessageSeverity.information
          pos      := ctx.fileMap.toPosition <| ctx.ref.getPos?.getD 0
          data     := output
        }
      return .mk {
        desc
        diagnostics := (← Language.Snapshot.Diagnostics.ofMessageLog msgs)
        traces := st.traceState
      } trees
    | .error e => panic! toString (← e.toMessageData.toString.toBaseIO).toOption

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
    let async ← preEnv.addConstAsync name kind
    async.commitConst async.asyncEnv (some info)
    setEnv async.mainEnv
    let ctx ← read
    let checkAct ← runAsync do
      try
        setEnv async.asyncEnv
        doAdd
        async.checkAndCommitEnv (← getEnv) ctx.options ctx.cancelTk?
      finally
        async.commitFailure
    let checkTask ← BaseIO.mapTask (t := preEnv.checked) fun _ =>
      EIO.catchExceptions checkAct fun e => do dbg_trace toString (← e.toMessageData.toString.toBaseIO).toOption
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
