/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public meta import Lean.PostprocessTraces.Basic
public meta import Lean.Elab.Command
import Lean.CoreM

/-!
# Experimental: Stored Traces

Iterating on a trace postprocessor with `postprocess_traces` re-runs the traced command on every
edit, which is impractical if the command is slow. `store_traces_as t in cmd` runs `cmd` once and
stores its trace messages under the name `t`; `#trace_roots t` and `#postprocess_traces t post`
then inspect the stored trace without re-running `cmd`.

Stored traces are kept in an in-memory environment extension and are only available in the file
that stored them; they are not exported to `.olean` files. `store_traces_as` declares
`t : CoreM StoredTrace`, which merely references the stored data, so that metaprograms can
inspect the trace as well.
-/

public section

namespace Lean.PostprocessTraces

open Lean.Elab.PostprocessTraces

/--
Experimental. `store_traces_as` and the library around it are expected to change in the future.

`store_traces_as t in cmd` runs `cmd`, reports its output unchanged, and additionally stores the
trace messages it produced under the name `t`. The stored trace can then be inspected
without re-running `cmd` using `#trace_roots t` and `#postprocess_traces t post`, which is useful
when `cmd` is slow and the right trace postprocessor is found iteratively.

`store_traces_as` also adds a declaration `t : CoreM Lean.PostprocessTraces.StoredTrace` to the
environment, so the trace can be inspected by arbitrary metaprograms, e.g.
`#eval do return (← t).roots.size`. The declaration only references the trace data, which is
kept in memory for the current file only; it is not exported to `.olean` files.
-/
scoped syntax (name := storeTracesAsCmd)
  "store_traces_as " ident " in" ppLine command : command

/--
Experimental. `#postprocess_traces` and the library around it are expected to change in the
future.

`#postprocess_traces t post` applies the trace postprocessor `post : TracePostprocessor` to the
trace stored as `t` by `store_traces_as t in cmd` and then renders the resulting trace tree.
See `postprocess_traces` for the available operations and patterns.
-/
scoped syntax (name := postprocessStoredTracesCmd)
  "#postprocess_traces " ident ppSpace term : command

/--
A trace stored by `store_traces_as t in cmd`, for inspection in metaprograms.

`store_traces_as` declares `t : CoreM StoredTrace`, so the stored trace can be retrieved in any
metaprogram that can run `CoreM`, e.g. `#eval do return (← t).roots.size`. The trace data itself
is kept in an in-memory environment extension and is only available in the file that stored it;
in particular, it is not exported to `.olean` files. The declaration only holds a reference, so
declaring it is cheap even for very large traces.
-/
structure StoredTrace where
  /--
  The stored trace messages: one message per source range inside the traced command, see
  `addTraceAsMessages`.
  -/
  messages : Array Message
  deriving Inhabited

private meta initialize storedTracesExt : EnvExtension (NameMap StoredTrace) ←
  registerEnvExtension (pure {})

/-- Returns the trace stored under the declaration `declName`, if any. -/
meta def findStoredTrace? (env : Environment) (declName : Name) : Option StoredTrace :=
  (storedTracesExt.getState env).find? declName

/-- The names of all traces stored in the current file, with their stored traces. -/
meta def allStoredTraces (env : Environment) : List (Name × StoredTrace) :=
  (storedTracesExt.getState env).toList

/--
Returns the trace stored under the declaration `declName`. This is the implementation of the
declarations created by `store_traces_as`; the trace data is only available in the file that
stored it.
-/
meta def findStoredTrace (declName : Name) : CoreM StoredTrace := do
  let some t := findStoredTrace? (← getEnv) declName
    | throwError "trace data for `{declName}` is not available in this context (stored traces \
        are kept in memory and are only available in the file that stored them)"
  return t

/-- Stores `t` under the declaration `declName`, overwriting any previously stored trace. -/
meta def storeTraces (declName : Name) (t : StoredTrace) : CoreM Unit :=
  modifyEnv (storedTracesExt.modifyState · (·.insert declName t))

namespace StoredTrace

/-- All trace trees of the stored trace, across all of its messages. -/
meta def trees (t : StoredTrace) : Array TraceTree :=
  t.messages.flatMap fun msg =>
    match traceContainer? msg.data with
    | some (_, roots) => roots.map TraceTree.ofMessageData
    | none            => #[]

/--
Applies a postprocessor to every trace message of the stored trace, dropping messages whose
roots were all removed.
-/
meta def postprocess (t : StoredTrace) (post : TracePostprocessor) : CoreM StoredTrace :=
  return ⟨← t.messages.filterMapM (postprocessMessage post ·)⟩

end StoredTrace

end Lean.PostprocessTraces

namespace Lean.Elab.PostprocessTraces
open Lean.PostprocessTraces Command

@[command_elab Lean.PostprocessTraces.storeTracesAsCmd]
meta def elabStoreTraceAs : CommandElab
  | `(command| store_traces_as $id in $cmd) => do
    -- the trace data is only available in the file that stored it, so the declaration is private
    let declName := mkPrivateName (← getEnv) ((← getScope).currNamespace ++ id.getId)
    let msgs ← runAndCollectMessages cmd
    -- report all messages of the command unchanged
    modify fun st => { st with messages := msgs.foldl (·.add ·) st.messages }
    -- Declare `declName : CoreM StoredTrace` so that the trace can be inspected by arbitrary
    -- metaprograms. The declaration body merely references the trace data, which is kept in an
    -- in-memory environment extension, so declaring it is cheap even for very large traces.
    liftCoreM <| addAndCompile (markMeta := true) <| .defnDecl {
      name        := declName
      levelParams := []
      type        := mkApp (mkConst ``CoreM) (mkConst ``Lean.PostprocessTraces.StoredTrace)
      value       := mkApp (mkConst ``Lean.PostprocessTraces.findStoredTrace) (toExpr declName)
      hints       := .abbrev
      safety      := .safe
    }
    liftCoreM <| addDocStringCore declName
      s!"A trace stored by `store_traces_as` (`{(← getFileName)}`); \
        inspect it with `#trace_roots {id.getId}` and \
        `#postprocess_traces {id.getId} <postprocessor>`, or in metaprograms, e.g. \
        `#eval do return (← {id.getId}).roots.size`."
    addDeclarationRangesFromSyntax declName (← getRef) id
    addConstInfo id declName
    liftCoreM <| storeTraces declName ⟨msgs.filter (·.isTrace)⟩
  | _ => throwUnsupportedSyntax

/--
Resolves the name of a trace stored by `store_traces_as` (relative to the current namespace,
like any other constant) and returns the stored trace, or throws an error listing the available
names.
-/
private meta def resolveStoredTrace (id : Ident) : CommandElabM StoredTrace := do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some t := findStoredTrace? (← getEnv) declName
    | let available := allStoredTraces (← getEnv) |>.map (m!"`{privateToUserName ·.1}`")
      let hint :=
        if available.isEmpty then
          m!"no traces have been stored in this file"
        else
          m!"stored traces: {MessageData.joinSep available ", "}"
      throwErrorAt id "unknown stored trace `{id.getId}` ({hint}); store one using `store_traces_as {id.getId} in <command>`"
  return t

@[command_elab Lean.PostprocessTraces.postprocessStoredTracesCmd]
meta def elabPostprocessStoredTraces : CommandElab
  | `(command| #postprocess_traces $id $post) => do
    let stored ← resolveStoredTrace id
    let post ← evalPostprocessorTopLevel post
    let stored ← liftCoreM <| stored.postprocess post
    -- anchor the output at the `#postprocess_traces` command itself, not at the original positions
    -- of the stored messages
    let ref ← getRef
    let pos := ref.getPos?.getD 0
    let endPos := ref.getTailPos?.getD pos
    for msg in stored.messages do
      logMessage <| mkMessageCore (← getFileName) (← getFileMap) msg.data .information pos endPos
  | _ => throwUnsupportedSyntax

end Lean.Elab.PostprocessTraces
