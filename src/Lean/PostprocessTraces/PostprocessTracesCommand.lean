/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public meta import Lean.PostprocessTraces.Basic
public meta import Lean.Elab.Command

/-!
# Experimental: the `postprocess_traces` command

`postprocess_traces post in cmd` runs `cmd` and transforms its trace messages with the trace
postprocessor `post` before they are reported. See `Lean.PostprocessTraces.Basic` for the
postprocessor library.
-/

public section

namespace Lean.PostprocessTraces

/--
Experimental. `postprocess_traces` and the library around it are expected to change in the future.

`postprocess_traces post in cmd` runs `cmd` and transforms every trace message it produces
with the trace postprocessor `post : Lean.PostprocessTraces.TracePostprocessor` before it is reported.

The postprocessor receives the array of trace roots of each trace message and returns the
transformed roots; returning an empty array drops the message entirely. The `Lean.PostprocessTraces`
namespace (automatically opened in `post`) provides operations such as `filterSubtrees`, `hoist`,
`exposeSubtrees`, and `selfTime`, which take patterns such as `ofClass`, `containsString`, and
`minTimeMs` and compose left-to-right with `>=>`. User-defined postprocessors and patterns are
ordinary functions.

For example, the following only shows the instance-synthesis steps that mention `tryResolve`,
together with their ancestors:
```lean
set_option trace.Meta.synthInstance true in
postprocess_traces filter (containsString "tryResolve") in
example : Inhabited (List Nat) := inferInstance
```
-/
scoped syntax (name := postprocessTracesCmd)
  "postprocess_traces " term " in" ppLine command : command

end Lean.PostprocessTraces

namespace Lean.Elab.PostprocessTraces
open Lean.PostprocessTraces Command

@[command_elab Lean.PostprocessTraces.postprocessTracesCmd]
meta def elabPostprocessTraces : CommandElab
  | `(command| postprocess_traces $post in $cmd) => do
    -- on errors in `post`, log them and fall back to the identity postprocessor so that `cmd`
    -- still elaborates, e.g. while the postprocessor term is being edited
    let post ← try
      evalPostprocessorTopLevel post
    catch ex =>
      logException ex
      pure fun roots => return roots
    for msg in ← runAndCollectMessages cmd do
      try
        if let some msg ← liftCoreM <| postprocessMessage post msg then
          modify fun st => { st with messages := st.messages.add msg }
      catch ex =>
        -- if the postprocessor fails at runtime, report the message unprocessed
        logException ex
        modify fun st => { st with messages := st.messages.add msg }
  | _ => throwUnsupportedSyntax

end Lean.Elab.PostprocessTraces
