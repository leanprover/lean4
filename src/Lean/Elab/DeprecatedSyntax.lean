/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.MonadEnv
public import Lean.Linter.Basic
public import Lean.Elab.Util

public section

namespace Lean.Linter

register_builtin_option linter.deprecated.syntax : Bool := {
  defValue := true
  descr := "if true, generate warnings when deprecated syntax is used"
}

end Lean.Linter

namespace Lean.Elab

/-- Entry recording that a syntax kind has been deprecated. -/
structure SyntaxDeprecationEntry where
  /-- The syntax node kind that is deprecated. -/
  kind : SyntaxNodeKind
  /-- Optional deprecation message. -/
  text? : Option String := none
  /-- Optional version or date at which the syntax was deprecated. -/
  since? : Option String := none

builtin_initialize deprecatedSyntaxExt :
    SimplePersistentEnvExtension SyntaxDeprecationEntry (NameMap SyntaxDeprecationEntry) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := mkStateFromImportedEntries (fun m e => m.insert e.kind e) {}
    addEntryFn := fun m e => m.insert e.kind e
  }

/--
Check whether `stx` is a deprecated syntax kind, and if so, emit a warning.

If `macroStack` is non-empty, the warning is attributed to the macro call site rather than the
syntax itself.
-/
def checkDeprecatedSyntax [Monad m] [MonadEnv m] [MonadLog m] [MonadOptions m]
    [AddMessageContext m] [MonadRef m] (stx : Syntax) (macroStack : MacroStack) : m Unit := do
  let env ← getEnv
  let kind := stx.getKind
  if let some entry := (deprecatedSyntaxExt.getState env).find? kind then
    let extraMsg := match entry.text? with
      | some text => m!": {text}"
      | none => m!""
    match macroStack with
    | { before := macroStx, .. } :: { before := callerStx, .. } :: _ =>
      let expandedFrom :=
        if callerStx.getKind != macroStx.getKind then
          m!" (expanded from '{callerStx.getKind}')"
        else m!""
      Linter.logLintIf Linter.linter.deprecated.syntax macroStx
        m!"macro '{macroStx.getKind}'{expandedFrom} produces deprecated syntax '{kind}'{extraMsg}"
    | { before := macroStx, .. } :: [] =>
      Linter.logLintIf Linter.linter.deprecated.syntax macroStx
        m!"macro '{macroStx.getKind}' produces deprecated syntax '{kind}'{extraMsg}"
    | [] =>
      Linter.logLintIf Linter.linter.deprecated.syntax stx
        m!"syntax '{kind}' has been deprecated{extraMsg}"

end Lean.Elab
