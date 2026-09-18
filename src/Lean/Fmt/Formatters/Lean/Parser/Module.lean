/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Parser.Module
import Lean.Fmt.FmtM.CommonFormatters
import Lean.Fmt.FmtM.Comments
import Init.Data
import Init.While

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Module.header]
public def fmtHeader : Fmt := fun
  | `(Parser.Module.header| $[module%$moduleTk?]? $[prelude%$preludeTk?]? $importsStx*) => do
    let moduleTk? ← fmt? moduleTk?
    let preludeTk? ← fmt? preludeTk?
    let imports ←
      importsStx.mapM fun
        | `(Parser.Module.import| $[public%$publicTk?]? $[meta%$metaTk?]? import%$importTk $[all%$allTk?]? $mod) =>
          do
            let publicTk? ← fmt? publicTk?
            let metaTk? ← fmt? metaTk?
            let importTk ← fmt importTk
            let allTk? ← fmt? allTk?
            let tks := Layouts.spacedAtomic #[publicTk?, metaTk?, importTk, allTk?]
            let mod ← fmt mod
            return Layouts.pseudoApplication #[tks, mod]
        | _ =>
          throw .partialFormatter
    return Layouts.spacedLines #[
      moduleTk?,
      Layouts.lines <| #[preludeTk?] ++ imports
    ]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Module.module]
public def fmtModule : Fmt := fun stx => do
  let Syntax.node _ ``Parser.Module.module #[
        headerStx,
        Syntax.node _ `Lean.Parser.Module.cmds cmdStxs
      ] :=
      stx
    | throw .partialFormatter
  let docs := (← headerDocs headerStx) ++ (← cmdDocs cmdStxs)
  return docs
where
  headerDocs (headerStx : Syntax) : FmtM TaggedDoc := do
    let headerLeading ← fmtLeadingWithRetainedNewlinesAndComments headerStx
    let headerDoc ← fmt headerStx
    let headerTrailing ← fmtTrailingWithRetainedNewlinesAndComments headerStx
    return headerLeading ++ headerDoc ++ headerTrailing
  cmdDocs (cmdStxs : Array Syntax) : FmtM TaggedDoc := do
    if cmdStxs.isEmpty then
      return empty
    let firstCmdLeading ← fmtLeadingWithRetainedNewlinesAndComments cmdStxs[0]!
    let cmdDocs ← fmtArrayWithRetainedIntermediateNewlinesAndComments cmdStxs
    let lastCmdTrailing ← fmtTrailingWithRetainedNewlinesAndComments cmdStxs[cmdStxs.size - 1]!
    return firstCmdLeading ++ cmdDocs ++ lastCmdTrailing
