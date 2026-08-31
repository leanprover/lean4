import Lean.Elab.Command

/-!
Verso docstrings on `coinductive` declarations and their constructors elaborate without errors
and are stored as elaborated Verso docstrings (issue #14233). Also checks that the docstring is visible to
attributes applied at `afterCompilation` time (matching `inductive` behavior) and that
diagnostics from docstring elaboration are reported exactly once.
-/

open Lean Elab Command Doc

private partial def inlineStr : Inline ElabInline → String
  | .text s => s
  | .code s => s!"code[{s}]"
  | .emph xs => s!"emph[{String.join (xs.map inlineStr).toList}]"
  | .bold xs => s!"bold[{String.join (xs.map inlineStr).toList}]"
  | .concat xs | .link xs _ | .footnote _ xs => String.join (xs.map inlineStr).toList
  | .other _ xs => s!"role[{String.join (xs.map inlineStr).toList}]"
  | _ => ""

private def blockKindAndText : Block ElabInline ElabBlock → String
  | .para inlines => s!"para: {String.join (inlines.map inlineStr).toList}"
  | .blockquote .. => "blockquote"
  | .ul .. => "ul"
  | .ol .. => "ol"
  | .dl .. => "dl"
  | .code .. => "code"
  | .concat .. => "concat"
  | .other .. => "other"

/-- Dumps the stored docstring of `name`: the literal Markdown string, or the Verso block dump. -/
elab "#dumpDoc " name:ident : command => do
  let env ← getEnv
  runTermElabM fun _ => do
    let declName ← realizeGlobalConstNoOverloadWithInfo name
    match (← findInternalDocString? env declName (includeBuiltin := true)) with
    | none => logInfo "none"
    | some (.inl md) => logInfo m!"markdown: {repr md}"
    | some (.inr doc) => logInfo m!"verso: {String.intercalate "; " (doc.text.map blockKindAndText).toList}"

set_option doc.verso true

-- The basic reproducer from #14233: a Verso docstring on a `coinductive` without binders.
#guard_msgs in
/-- a doc string -/
coinductive Approximates : Prop

/-- info: verso: para: a doc string -/
#guard_msgs in #dumpDoc Approximates

-- A `coinductive` with binders; the docstrings reference a parameter by name.
#guard_msgs in
/-- If {lean}`r` relates things. -/
coinductive infSeqDoc (r : Nat → Nat → Prop) : Nat → Prop where
  /-- One {lean}`r` step. -/
  | step : r a b → infSeqDoc r b → infSeqDoc r a

/-- info: verso: para: If role[code[r]] relates things. -/
#guard_msgs in #dumpDoc infSeqDoc

/-- info: verso: para: One role[code[r]] step. -/
#guard_msgs in #dumpDoc infSeqDoc.step

-- Constructor docstrings on a `coinductive`.
#guard_msgs in
coinductive withCtorDoc : Prop where
  /-- ctor doc -/
  | mk : withCtorDoc

/-- info: verso: para: ctor doc -/
#guard_msgs in #dumpDoc withCtorDoc.mk

-- The docstring can reference the declaration's own constructors.
#guard_msgs in
/-- Built by {lean}`selfRef.mk`. -/
coinductive selfRef : Prop where
  | mk : selfRef

/-- info: verso: para: Built by role[code[selfRef.mk]]. -/
#guard_msgs in #dumpDoc selfRef

-- Mutual blocks mixing `coinductive` and `inductive`.
#guard_msgs in
mutual
  /-- tick doc -/
  coinductive tickDoc : Prop where
    /-- tick ctor doc -/
    | mk : ¬tockDoc → tickDoc

  /-- tock doc -/
  inductive tockDoc : Prop where
    /-- tock ctor doc -/
    | mk : ¬tickDoc → tockDoc
end

/-- info: verso: para: tick doc -/
#guard_msgs in #dumpDoc tickDoc

/-- info: verso: para: tock doc -/
#guard_msgs in #dumpDoc tockDoc

/-- info: verso: para: tick ctor doc -/
#guard_msgs in #dumpDoc tickDoc.mk

/-- info: verso: para: tock ctor doc -/
#guard_msgs in #dumpDoc tockDoc.mk

-- Diagnostics from elaborating the docstring are reported exactly once.
@[deprecated "It is gone." (since := "2026-01-01")]
def oldThing := 0

set_option linter.deprecated true in
/-- warning: `oldThing` has been deprecated: It is gone. -/
#guard_msgs in
/-- Uses {lean}`oldThing`. -/
coinductive diagOnce : Prop

set_option doc.verso false

-- Markdown docstrings on `coinductive` types and constructors are stored as Markdown.
#guard_msgs in
/-- md doc -/
coinductive mdCo : Prop where
  /-- md ctor doc -/
  | mk : mdCo

/-- info: markdown: "md doc " -/
#guard_msgs in #dumpDoc mdCo

/-- info: markdown: "md ctor doc " -/
#guard_msgs in #dumpDoc mdCo.mk

/-!
The docstring must already be present when `afterCompilation` attributes run, as it is for
`inductive`: `@[inherit_doc]` detects the existing docstring.
-/

/-- warning: mdOrder already has a doc string -/
#guard_msgs in
/-- existing -/
@[inherit_doc Nat.add]
coinductive mdOrder : Prop

set_option doc.verso true

/-- warning: versoOrder already has a doc string -/
#guard_msgs in
/-- existing -/
@[inherit_doc Nat.add]
coinductive versoOrder : Prop
