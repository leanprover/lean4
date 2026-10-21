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


/--
Parses the inline content of the blocks identified in a Markdown document using `parseInlines`. This
is the second pass of the algorithm suggested in the CommonMark specification. Two passes are
necessary because the presence of a link definition later in the document affects the syntactic
interpretation of reference-style links earlier in the document.
-/
partial def parseInlinesInBlock (refs : RefTable) (s : String) :
    Block Syntax.Range → Block (Array Inline)
  | .paragraph lines =>
    let src := InlineSource.ofLines s lines
    .paragraph #[parseInlines refs src { start := src.startPos, stop := src.stopPos }]
  | .atxHeading level hashes content closeHashes? =>
    .atxHeading level hashes (parseInlines refs (.ofRange s content) content) closeHashes?
  | .setextHeading level lines underline =>
    let src := InlineSource.ofLines s lines
    .setextHeading level
      #[parseInlines refs src { start := src.startPos, stop := src.stopPos }]
      underline
  | .fencedCode info openFence closeFence? lines =>
    .fencedCode info openFence closeFence? lines
  | .indentedCode lines =>
    .indentedCode lines
  | .blockquote markers children =>
    .blockquote markers (children.map (parseInlinesInBlock refs s))
  | .list kind tight items =>
    .list kind tight (items.map (parseInlinesInBlock refs s))
  | .listItem marker children =>
    .listItem marker (children.map (parseInlinesInBlock refs s))
  | .linkRefDef m =>
    .linkRefDef m
  | .thematicBreak line =>
    .thematicBreak line

/--
Parses a Markdown string, delimited by `startPos` and `endPos`.

This parser is based on the two-pass algorithm specified in the CommonMark specification.
-/
public def parseDocument (s : String) (startPos endPos : String.Pos.Raw) :
    Array (Block (Array Inline)) :=
  let blocks := parseBlocks s startPos endPos
  let refs := buildRefTable s blocks
  blocks.map (parseInlinesInBlock refs s)
