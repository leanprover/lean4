/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Lean.PostprocessTraces.Basic
public import Lean.PostprocessTraces.PostprocessTracesCommand
public import Lean.PostprocessTraces.StoredTraces
public import Lean.PostprocessTraces.Postprocessors

/-!
# Experimental: Trace Postprocessors

Trace messages of complex elaboration tasks can be large, and finding the relevant part in
the editor requires a lot of clicking and searching. This module provides trace postprocessors:
functions that transform the trace of a command before it is reported, e.g. by filtering out
irrelevant subtrees, hoisting the interesting ones, or pre-expanding the paths to matches.

A trace postprocessor (`Lean.PostprocessTraces.TracePostprocessor`) receives the array of trace
trees of one trace message and returns the transformed trees. The `Lean.PostprocessTraces` namespace
provides a small set of operations (`filterSubtrees`, `hoist`, `exposeSubtrees`, `countNodes`,
`selfTime`) that compose left-to-right with `>=>`. The selecting operations take a pattern
(`Lean.PostprocessTraces.TracePattern`), a predicate on trace subtrees; built-in patterns select by
trace class (`ofClass`), text (`containsString`), result (`succeeded`, `failed`, `errored`,
`unsuccessful`), and time (`minTimeMs`, `minSelfTimeMs`). Users can define their own postprocessors
and patterns as ordinary functions.

Entry points:
- `postprocess_traces post in cmd` (see `Lean.PostprocessTraces.Command`) transforms the trace
  messages produced by `cmd` with `post`.
- `store_traces_as t in cmd` (see `Lean.PostprocessTraces.StoredTraces`) stores the trace messages of
  `cmd` under the name `t`, so that slow commands do not have to be re-run while iterating on a
  postprocessor.

Traces are stored as `MessageData` (see `MessageData.trace`); `TraceTree` is a structured view of
such messages that takes care of the context wrappers (`MessageData.withContext` etc.) around
trace nodes.
-/
