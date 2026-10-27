/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Linter.Util
public import Lean.Elab.Command
import Lean.Fmt.FmtM

public section

namespace Lean.Linter

open Lean Elab.Command

register_builtin_option linter.fmt.missing : Bool := {
  defValue := false
  descr := "enable the 'missing formatter' linter"
}

register_builtin_option linter.fmt.missing.ignorePrivate : Bool := {
  defValue := false
  descr :=
    "make the 'missing formatter' linter ignore syntax with a private node kind, which is \
      what `local syntax`, `local macro` and `local notation` produce"
}

/--
Whether `kind` is exempt from being reported. A private kind stems from a `local` syntax
declaration, whose mangled kind no formatter can name.
-/
private def isIgnoredKind (opts : Options) (kind : Name) : Bool :=
  kind == nullKind || (linter.fmt.missing.ignorePrivate.get opts && isPrivateName kind)

private def checkMissingFormatter (stx : Syntax) : CommandElabM Unit := do
  let env ← getEnv
  let text ← getFileMap
  let opts ← getOptions
  let infoState ← Elab.getInfoState
  -- Forced only when the formatter hits a `choice` node whose alternatives render differently.
  -- `runLintersAsync` hands linters an already substituted info state, so forcing this waits on
  -- nothing there.
  let infoTrees : Thunk (PersistentArray Elab.InfoTree) :=
    .mk fun _ => infoState.substituteLazy.get.trees
  let lineInfos := Fmt.collectSyntaxLineInfos stx
  let ctx := {
    env
    text
    resolveChoiceNode := fun range => infoTrees.get.findSome? (Fmt.findChoiceResolution? · range)
    opts
    lineInfos
  }
  -- An aborting error hides all missing formatters of the command, so it is reported as well.
  let r ←
    match FmtM.run ctx (Fmt.fmt stx) with
    | .ok r =>
      pure r
    | .error e =>
      let ref := e.ref? |>.getD stx
      logLint linter.fmt.missing ref <|
        m!"The auto-formatter failed, so this command was not checked for missing formatters:\n\n"
          ++ toString e
      return
  for (range, missingFormatter) in r.missingFormatters do
    if isIgnoredKind opts missingFormatter.kind then continue
    logLint linter.fmt.missing (.ofRange range)
      m!"no auto-formatter registered for syntax kind {Expr.const missingFormatter.kind []}"
  for (range, partialFormatter) in r.partialFormatters do
    let kind := partialFormatter.stx.getKind
    if isIgnoredKind opts kind then continue
    let fmtName :=
      if !partialFormatter.formatterName.isAnonymous then
        m!"{Expr.const partialFormatter.formatterName []} "
      else
        m!""
    logLint linter.fmt.missing (.ofRange range) <|
      m!"Auto-formatter {fmtName}for syntax kind {Expr.const kind []} is incomplete.\n"
        ++ m!"The syntax at the location has the following form:\n\n"
        ++ toString partialFormatter.stx

/--
Linter that warns about syntax nodes for which no auto-formatter is registered.
The linter notes the `SyntaxNodeKind` in the warning message.

Set `linter.fmt.missing.ignorePrivate` to skip syntax declared with `local`.
-/
def fmtMissing : Linter where
  run cmdStx := do
    unless linter.fmt.missing.get (← getLinterOptions).toOptions do
      return
    -- `missing` nodes from parser error recovery make formatters fail, which would be reported as
    -- spurious incomplete formatters. The formatter entry points reject such input as well.
    if cmdStx.hasMissing then
      return
    checkMissingFormatter cmdStx

builtin_initialize addLinter fmtMissing

end Lean.Linter
