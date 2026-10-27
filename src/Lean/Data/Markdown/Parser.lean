/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Lean.Data.Markdown.Parser.Block
public import Lean.Data.Markdown.Parser.Inline

namespace Lean.Markdown


variable {s : String.Slice}

/--
Parses the inline content of a block from the first pass, with `refs` set to the document's link
reference definitions. This is the second pass of the algorithm described in the CommonMark
specification.

Two passes are necessary because the presence of a link definition later in the document affects the
syntactic interpretation of reference-style links earlier in the document.
-/
public partial def parseInlinesInBlock (refs : RefTable s) (block : Block.Raw s)
    (extensions : Extensions := {}) : Block s :=
  match block with
  | .paragraph content =>
    .paragraph (parseInlines refs content extensions)
  | .atxHeading level hashes content closeHashes? =>
    .atxHeading level hashes (parseInlines refs content extensions) closeHashes?
  | .setextHeading level content underline =>
    .setextHeading level (parseInlines refs content extensions) underline
  | .fencedCode info openFence closeFence? lines =>
    .fencedCode info openFence closeFence? lines
  | .indentedCode lines =>
    .indentedCode lines
  | .html lines =>
    .html lines
  | .blockquote markers children =>
    .blockquote markers (children.map (parseInlinesInBlock refs · extensions))
  | .list kind tight items =>
    .list kind tight (items.map (parseInlinesInBlock refs · extensions))
  | .listItem marker children =>
    .listItem marker (children.map (parseInlinesInBlock refs · extensions))
  | .linkRefDef m =>
    .linkRefDef m
  | .thematicBreak line =>
    .thematicBreak line

/--
Parses `s` as a Markdown document.

Up to `indent` leading spaces of each line are skipped.

By default, the parser adheres to CommonMark with one exception: it compares link labels modulo
Unicode case folding only for the Latin-1 and Greek ranges, while CommonMark specifies full Unicode
case folding. Use `extensions` to enable non-standard extensions like LaTeX math.

The `externalRefs` table maps labels to reference definitions beyond the document's own link
reference definitions. Its labels are normalized like those in the document. A reference definition
in the document takes precedence over an external definition with the same label unless the external
definition has `overrideDocument` set.

This parser is based on the two-pass algorithm described in the CommonMark specification.
-/
public def parseDocument (s : String.Slice) (indent : Nat := 0) (extensions : Extensions := {})
    (externalRefs : Std.HashMap String ExternalRef := {}) : Array (Block s) :=
  let blocks := parseBlocks s indent
  let refs := buildRefTable blocks externalRefs
  blocks.map (parseInlinesInBlock refs · extensions)
