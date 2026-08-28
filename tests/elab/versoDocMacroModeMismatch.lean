import Lean

/-!
This test ensures that docstrings in syntax produced by macros are processed correctly, even in
contexts where `doc.verso` has a different value that the quotation's parse site.

All four combinations of (definition-site format) × (invocation-site format) are covered.
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

/-
A macro defined where `doc.verso` is off: its `/-- ... -/` is parsed as Markdown. `{x}` is literal
text, not Verso role syntax.
-/
section
set_option doc.verso false
macro "mdMacro" nm:ident : command => `(/-- The set {x} is a singleton. -/ def $nm := 0)
end

/-
A macro defined where `doc.verso` is on: its `/-- ... -/` is parsed as a Verso AST. `{lean}` is a
role applied to inline code.
-/
section
set_option doc.verso true
macro "versoMacro" nm:ident : command => `(/-- Uses {lean}`Nat.succ`. -/ def $nm := 0)
end

-- Markdown definition site, Markdown invocation site: stored as Markdown.
#guard_msgs in
set_option doc.verso false in
mdMacro caseMdMd

/-- info: markdown: "The set {x} is a singleton. " -/
#guard_msgs in #dumpDoc caseMdMd

-- Markdown definition site, Verso invocation site: stored as Markdown (definition site wins). The
-- literal `{x}` must not be re-parsed as Verso role syntax.
#guard_msgs in
set_option doc.verso true in
mdMacro caseMdVerso

/-- info: markdown: "The set {x} is a singleton. " -/
#guard_msgs in #dumpDoc caseMdVerso

-- Verso definition site, Markdown invocation site: stored as Verso (definition site wins). The Verso
-- AST must not be handed to the Markdown text extractor.
#guard_msgs in
set_option doc.verso false in
versoMacro caseVersoMd

/-- info: verso: para: Uses role[code[Nat.succ]]. -/
#guard_msgs in #dumpDoc caseVersoMd

-- Verso definition site, Verso invocation site: stored as Verso.
#guard_msgs in
set_option doc.verso true in
versoMacro caseVersoVerso

/-- info: verso: para: Uses role[code[Nat.succ]]. -/
#guard_msgs in #dumpDoc caseVersoVerso

/-
Sanity: ordinary (non-macro) declarations still store the form selected by `doc.verso` at their own
site.
-/
set_option doc.verso false in
/-- Uses {lean}`Nat.succ` literally. -/
def plainMarkdown := 0

/-- info: markdown: "Uses {lean}`Nat.succ` literally. " -/
#guard_msgs in #dumpDoc plainMarkdown

set_option doc.verso true in
/-- Uses {lean}`Nat.succ`. -/
def plainVerso := 0

/-- info: verso: para: Uses role[code[Nat.succ]]. -/
#guard_msgs in #dumpDoc plainVerso
