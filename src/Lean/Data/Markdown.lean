/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Lean.Data.Markdown.Unicode.CaseFolding
public import Lean.Data.Markdown.Unicode.CharacterClasses
public import Lean.Data.Markdown.Inline
public import Lean.Data.Markdown.Block
public import Lean.Data.Markdown.Text
public import Lean.Data.Markdown.Parser

/-!
# Markdown Parser

A CommonMark parser that records the source range of every construct. The Lean language server uses
it to provide semantic tokens inside Markdown docstrings. The entry point is
`Lean.Markdown.parseDocument`.

The implementation follows CommonMark 0.31.2, with one deviation: link labels are case folded for
ASCII, Latin-1, and Greek letters, and compared case-sensitively for all other characters.

The parser additionally supports one optional non-standard extension: LaTeX-style math in `$…$` and
`$$…$$`.
-/
