/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Lean.PostprocessTraces.PostprocessTracesCommand
meta import Lean.PostprocessTraces.StoredTraces
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.PostprocessTraces.storeTracesAsCmd]
public def fmtStoreTracesAsCmd : Fmt := fun
  | `(Lean.PostprocessTraces.storeTracesAsCmd|
      store_traces_as%$storeTk $traceId:ident in%$inTk $cmd:command) =>
    fmtTracedCommand storeTk traceId inTk cmd
  | _ => throw .partialFormatter

@[builtin_fmt Lean.PostprocessTraces.postprocessStoredTracesCmd]
public def fmtPostprocessStoredTracesCmd : Fmt := fun
  | `(Lean.PostprocessTraces.postprocessStoredTracesCmd|
      #postprocess_traces%$postprocessTk $traceId:ident $post:term) => do
    let postprocessTk ← fmt postprocessTk
    let traceId ← fmt traceId
    let post ← fmt post
    return Layouts.pseudoApplication #[postprocessTk, traceId, post]
  | _ => throw .partialFormatter
