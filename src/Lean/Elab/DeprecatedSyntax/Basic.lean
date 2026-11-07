/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.MonadEnv
public import Lean.Linter.Init
public import Lean.Elab.Util
import Lean.Meta.Hint
import Lean.Elab.DeprecatedSyntax.FormatReplacement

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

private def insertReplacement (m : NameMap Name) : SyntaxNodeKind × Option Name → NameMap Name
  | (kind, some declName) => m.insert kind declName
  | (kind, none) => m.erase kind

/--
Maps each deprecated syntax kind to the `Macro` declaration generated from the alternatives of the
latest `deprecated_syntax` command for that kind, if any.
-/
builtin_initialize deprecatedSyntaxReplacementExt :
    SimplePersistentEnvExtension (SyntaxNodeKind × Option Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := mkStateFromImportedEntries insertReplacement {}
    addEntryFn := insertReplacement
  }

/-- Whether `kind` is marked by `deprecated_syntax`. -/
def isDeprecatedSyntax (env : Environment) (kind : SyntaxNodeKind) : Bool :=
  (deprecatedSyntaxExt.getState env).contains kind

private unsafe def evalReplacementUnsafe (declName : Name) : CoreM Macro :=
  evalConstCheck Macro ``Macro declName

@[implemented_by evalReplacementUnsafe]
private opaque evalReplacement (declName : Name) : CoreM Macro

/--
Creates a hint offering to replace `stx` by the output of the replacement registered for its kind.
Returns the empty message if there is no replacement or it fails.
-/
private def mkReplacementHint (stx : Syntax) : CoreM MessageData := do
  let env ← getEnv
  let some declName := (deprecatedSyntaxReplacementExt.getState env).find? stx.getKind
    | return .nil
  -- Printing the replacement requires its category, so it must be unambiguous
  let #[cat] := Parser.getSyntaxNodeKindCategories env stx.getKind | return .nil
  let some range := stx.getRange? (canonicalOnly := true) | return .nil
  -- Syntax that a metaprogram parsed from a string has positions in that string, not in the file
  unless stx.getSubstring?.map (·.str) |>.isEqSome (← getFileMap).source do return .nil
  -- Elaborators may rewrite syntax before elaborating it, e.g. by lifting nested actions out of a
  -- `do` element, and the replacement of such syntax does not reflect the source
  let isRewritten (s : Syntax) := (s.isAtom || s.isIdent) && !(s.getHeadInfo matches .original ..)
  if (stx.find? isRewritten).isSome then return .nil
  -- A failing replacement, even one exceeding a resource limit, must not prevent the warning
  tryCatchRuntimeEx
    (do
      let replacement ← evalReplacement declName
      -- The trailing trivia of `stx` is not replaced, so it must not be printed in the replacement
      let newStx :=
        (← withRef stx <| liftMacroM <| replacement stx.unsetTrailing).eraseQuoteMacroScopes
      let text ← DeprecatedSyntax.formatReplacement cat stx newStx range
      MessageData.hint "Replace the deprecated syntax:"
        #[{ suggestion := text }] (ref? := stx))
    fun _ => return .nil

private def SyntaxDeprecationEntry.textSuffix (entry : SyntaxDeprecationEntry) : MessageData :=
  match entry.text? with
  | some text => m!": {text}"
  | none => m!""

/--
Check whether `stx` is a deprecated syntax kind, and if so, emit a warning.

If `stx` was written by the user (its head token has `.original` source info), the warning is
attributed to the syntax itself even inside a macro expansion: enclosing macros (e.g. the internal
`namespace` expansion of `def Foo.bar ...`) merely passed the user's syntax through. Only
macro-generated syntax (synthetic source info, as produced by syntax quotations) is attributed to
the macro call site via `macroStack`. Replacement suggestions are only offered for syntax written by
the user.
-/
def checkDeprecatedSyntax (stx : Syntax) (macroStack : MacroStack) : CoreM Unit := do
  let env ← getEnv
  let kind := stx.getKind
  if let some entry := (deprecatedSyntaxExt.getState env).find? kind then
    unless Linter.getLinterValue Linter.linter.deprecated.syntax (← Linter.getLinterOptions) do
      return
    unless (← Core.shouldCheckDeprecated stx) do
      return
    let extraMsg := entry.textSuffix
    if stx.getHeadInfo matches .original .. then
      Linter.logLint Linter.linter.deprecated.syntax stx
        (m!"syntax '{kind}' has been deprecated{extraMsg}" ++ (← mkReplacementHint stx))
      return
    match macroStack with
    | { before := macroStx, .. } :: { before := callerStx, .. } :: _ =>
      let expandedFrom :=
        if callerStx.getKind != macroStx.getKind then
          m!" (expanded from '{callerStx.getKind}')"
        else m!""
      Linter.logLint Linter.linter.deprecated.syntax macroStx
        m!"macro '{macroStx.getKind}'{expandedFrom} produces deprecated syntax '{kind}'{extraMsg}"
    | { before := macroStx, .. } :: [] =>
      Linter.logLint Linter.linter.deprecated.syntax macroStx
        m!"macro '{macroStx.getKind}' produces deprecated syntax '{kind}'{extraMsg}"
    | [] =>
      Linter.logLint Linter.linter.deprecated.syntax stx
        m!"syntax '{kind}' has been deprecated{extraMsg}"

/--
Check whether `stx`, which is part of a syntax quotation, is a deprecated syntax kind, and if so,
emit a warning.

Syntax produced by expanding macros in the quotation (synthetic source info) is not reported: it is
not part of the quotation, and elaborating the result of the quotation reports it as produced by
these macros.
-/
def checkDeprecatedQuotedSyntax (stx : Syntax) : CoreM Unit := do
  let some entry := (deprecatedSyntaxExt.getState (← getEnv)).find? stx.getKind | return
  if stx.getHeadInfo matches .synthetic .. then return
  unless Linter.getLinterValue Linter.linter.deprecated.syntax (← Linter.getLinterOptions) do
    return
  unless (← Core.shouldCheckDeprecated stx) do
    return
  Linter.logLint Linter.linter.deprecated.syntax stx
    (m!"quotation uses deprecated syntax '{stx.getKind}'{entry.textSuffix}" ++
      (← mkReplacementHint stx))

end Lean.Elab
