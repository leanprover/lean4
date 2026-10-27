/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.PostprocessTraces.PostprocessTracesCommand
import Init.Data

namespace Lean.Fmt

/-- Formats the `<keyword> <arg> in <command>` trace commands. -/
public def fmtTracedCommand
    (keywordTk : Syntax) (arg : Syntax) (inTk : Syntax) (cmd : TSyntax `command)
    : FmtM TaggedDoc := do
  let keywordTk ← fmt keywordTk
  let arg ← fmt arg
  let inTk ← fmt inTk
  let cmd ← fmt cmd
  let signature := Layouts.pseudoApplication #[keywordTk, arg]
  return Layouts.keywordSeparated signature inTk cmd {
    allowFlattening := false
    nestedRhs := false
  }

@[builtin_fmt Lean.PostprocessTraces.postprocessTracesCmd]
public def fmtPostprocessTracesCmd : Fmt := fun
  | `(Lean.PostprocessTraces.postprocessTracesCmd|
      postprocess_traces%$postprocessTk $post:term in%$inTk $cmd:command) =>
    fmtTracedCommand postprocessTk post inTk cmd
  | _ =>
    throw .partialFormatter
