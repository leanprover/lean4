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
Parses the inline content of the blocks identified in a Markdown document using `parseInlines`. This
is the second pass of the algorithm suggested in the CommonMark specification. Two passes are
necessary because the presence of a link definition later in the document affects the syntactic
interpretation of reference-style links earlier in the document.
-/
partial def parseInlinesInBlock (refs : RefTable s) : Block.Raw s → Block s
  | .paragraph lines =>
    let src := InlineSource.ofLines lines
    .paragraph (parseInlines refs src src.startPos src.stopPos)
  | .atxHeading level hashes content closeHashes? =>
    .atxHeading level hashes
      (parseInlines refs (.ofRange content) content.startInclusive content.endExclusive) closeHashes?
  | .setextHeading level lines underline =>
    let src := InlineSource.ofLines lines
    .setextHeading level (parseInlines refs src src.startPos src.stopPos) underline
  | .fencedCode info openFence closeFence? lines =>
    .fencedCode info openFence closeFence? lines
  | .indentedCode lines =>
    .indentedCode lines
  | .blockquote markers children =>
    .blockquote markers (children.map (parseInlinesInBlock refs))
  | .list kind tight items =>
    .list kind tight (items.map (parseInlinesInBlock refs))
  | .listItem marker children =>
    .listItem marker (children.map (parseInlinesInBlock refs))
  | .linkRefDef m =>
    .linkRefDef m
  | .thematicBreak line =>
    .thematicBreak line

/--
Parses `s` as a Markdown document. Up to `indent` leading spaces of each line are skipped.

This parser is based on the two-pass algorithm specified in the CommonMark specification.
-/
public def parseDocument (s : String.Slice) (indent : Nat := 0) : Array (Block s) :=
  let blocks := parseBlocks s indent
  let refs := buildRefTable blocks
  blocks.map (parseInlinesInBlock refs)
