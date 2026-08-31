/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Lean.Server.FileWorker.Markdown.Basic
public import Lean.Server.FileWorker.Markdown.Parser

/-!
# Markdown parser for the language server

A CommonMark parser used by the Lean language server to provide semantic token highlighting inside
Markdown docstrings. The entry point is `Lean.Server.FileWorker.Markdown.parseDocument`.

The implementation follows CommonMark 0.31.2 closely with a small set of deviations:
* HTML blocks and inline HTML are not parsed.
* Link labels are compared case-insensitively only for the English letters A-Z, and case-sensitively
  for all other characters.
* Named character entities are not validated against the set of HTML entities.
-/
