/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
import Init
public import Lean.Server.FileWorker.Markdown.Basic

public section

namespace Lean.Server.FileWorker.Markdown

/-!
## The In-Progress Zipper

While identifying the block structure of a document, lines are checked one at a time and added in
order. A zipper-like structure makes it easy to see the surrounding block context and to modify it
at the right-hand edge.
-/

/--
A container that is currently open and may still receive child blocks.
-/
inductive OpenContainer where
  /--
  A blockquote. `markers` accumulates the positions of `>` markers from
  every continuation line that has been seen so far.
  -/
  | blockquote (markers : Array Syntax.Range)
  /-- A list. -/
  | list (kind : ListKind)
  /--
  A list item.

  - `marker` is this item's bullet or ordered-marker range, emitted as a
    delimiter token at item-open time.
  - `contentColumn` is the column at which the item's content begins;
    subsequent lines must be indented to at least this column to count as
    continuations of this item (CommonMark §5.2).
  -/
  | listItem (marker : Syntax.Range) (contentColumn : Nat)
deriving Repr, Inhabited

/--
A frame of the zipper's spine: an open container plus the children that have
already been closed inside it, in source order.
-/
structure ZipperFrame where
  /--
  The container in this frame. Subsequent frames in the stack represent the last child of this open
  container.
  -/
  container : OpenContainer
  /--
  Children that have already been closed inside this frame's container.
  -/
  closedChildren : Array (Block Syntax.Range) := #[]
  /--
  For list frames: set when a blank line followed by more content in this list has been observed
  during parsing.
  -/
  loose : Bool := false
deriving Inhabited

/-- A leaf block that is currently open and may still accept additional source lines. -/
inductive OpenLeaf where
  /--
  An open paragraph being extended line by line. Closing the paragraph (because of a blank line, a
  new block opener, or the parent container closing) finalizes it as `Block.paragraph`.
  -/
  | paragraph (lines : Array Syntax.Range)
  /--
  An open fenced code block. `lines` accumulates content lines until either a matching closing fence
  appears (yielding `Block.fencedCode` with `closeFence? := some _`) or the parent container closes
  at EOF (yielding `closeFence? := none`).
  -/
  | fencedCode (info : FenceInfo) (openFence : Syntax.Range) (lines : Array Syntax.Range)
  /--
  An open indented code block.

  - `lines` are the content lines committed so far. Each element is a pair of the line's source
    range (covering the whole source line, including the indent the block consumed) and the
    rendered string. In the rendered string, the 4 cols of indent that defined the code block
    (relative to the parent container's content column) have already been stripped, with any
    partial tabs materialized per CommonMark §2.2.
  - `pendingBlanks` holds blank lines that may belong to this block: they are promoted to `lines`
    when a subsequent indented line continues the block, and discarded when an unindented non-blank
    line closes the block. This matches CommonMark's rule that blank lines between indented chunks
    are part of the code block, but blank lines following the final chunk are not.
  -/
  | indentedCode (lines : Array (Syntax.Range × String))
      (pendingBlanks : Array (Syntax.Range × String))
deriving Inhabited

/--
The block parsing state. Maintains the spine of currently-open containers
plus an optional open leaf at the bottom.

An empty spine means that only the document is open.

Invariants (preserved by the zipper operations defined elsewhere):
- If `openLeaf?` is `some _`, that leaf logically lives inside the deepest
  spine frame, or directly under the document if the spine is empty;
  extending the leaf adds to its content, and closing the leaf pushes a
  `Block` onto that container's children.
- A `OpenContainer.list` frame's immediate spine successor (when present) is
  always an `OpenContainer.listItem`.
-/
structure BlockZipper where
  /-- Closed children of the document root, in source order. -/
  documentChildren : Array (Block Syntax.Range) := #[]
  /-- Open containers below the document root, deepest last. -/
  spine : Array ZipperFrame := #[]
  /-- An open leaf node, if one is present. -/
  openLeaf? : Option OpenLeaf := none
  /--
  Whether the previous source line was blank (after consuming the current open containers'
  prefixes). Used to mark enclosing lists as loose when a blank line is followed by content that
  continues the list (CommonMark §5.3).
  -/
  lastWasBlank : Bool := false
deriving Inhabited

namespace BlockZipper

/-- A zipper with only the document root open, no children, and no open leaf. -/
def empty : BlockZipper := {}

/-- The deepest currently-open container, or `none` if only the document is open. -/
def top? (z : BlockZipper) : Option OpenContainer :=
  z.spine.back?.map (·.container)

/--
Converts an open leaf into its closed `Block` form. Fenced code blocks are not terminated with a
fence.
-/
def leafToBlock : OpenLeaf → Block Syntax.Range
  | .paragraph lines => .paragraph lines
  | .fencedCode info openFence lines => .fencedCode info openFence none lines
  | .indentedCode lines _pendingBlanks => .indentedCode lines

/--
Pushes a finalized block onto the deepest spine frame's `closedChildren`, or directly onto
`documentChildren` if the spine is empty.
-/
private def pushChild (z : BlockZipper) (b : Block Syntax.Range) : BlockZipper :=
  if z.spine.isEmpty then
    { z with documentChildren := z.documentChildren.push b }
  else
    { z with
      spine :=
        z.spine.modify (z.spine.size - 1)
          (fun frame => { frame with closedChildren := frame.closedChildren.push b }) }

/-- Closes any open leaf, attaching it to the deepest container. -/
def closeLeaf (z : BlockZipper) : BlockZipper :=
  match z.openLeaf? with
  | none => z
  | some leaf =>
    let z := z.pushChild (leafToBlock leaf)
    { z with openLeaf? := none }

/-- Pushes a new container onto the spine, closing any open leaf first. -/
def openContainer (z : BlockZipper) (c : OpenContainer) : BlockZipper :=
  let z := z.closeLeaf
  { z with spine := z.spine.push { container := c } }

/-- Replaces the open leaf at the bottom of the spine, closing any prior one. -/
def openLeaf (z : BlockZipper) (l : OpenLeaf) : BlockZipper :=
  let z := z.closeLeaf
  { z with openLeaf? := some l }

/--
Adds a finalized block as a child of the deepest open container, closing any open leaf first. Used
for blocks like ATX headings that don't go through `OpenLeaf`.
-/
def addBlock (z : BlockZipper) (b : Block Syntax.Range) : BlockZipper :=
  z.closeLeaf.pushChild b

/-- Appends a source line to the open paragraph, if any. No-op otherwise. -/
def extendParagraph (z : BlockZipper) (line : Syntax.Range) : BlockZipper :=
  match z.openLeaf? with
  | some (.paragraph lines) =>
    { z with openLeaf? := some (.paragraph (lines.push line)) }
  | _ => z

/-- Appends a verbatim line to the open fenced code block, if any. No-op otherwise. -/
def extendFencedCode (z : BlockZipper) (line : Syntax.Range) : BlockZipper :=
  match z.openLeaf? with
  | some (.fencedCode info openFence lines) =>
    { z with openLeaf? := some (.fencedCode info openFence (lines.push line)) }
  | _ => z

/-- Closes the open fenced code block with a matching closing fence. -/
def closeFencedCode (z : BlockZipper) (closeFence : Syntax.Range) : BlockZipper :=
  match z.openLeaf? with
  | some (.fencedCode info openFence lines) =>
    let z := z.pushChild (.fencedCode info openFence (some closeFence) lines)
    { z with openLeaf? := none }
  | _ => z

/--
Appends an indented content line to the open indented code block. Any pending blanks held since the
last content line are promoted to real content lines first.
-/
def indentedCodeAddLine (z : BlockZipper) (range : Syntax.Range) (rendered : String) :
    BlockZipper :=
  match z.openLeaf? with
  | some (.indentedCode lines pendingBlanks) =>
    let newLines := lines ++ pendingBlanks ++ #[(range, rendered)]
    { z with openLeaf? := some (.indentedCode newLines #[]) }
  | _ => z

/--
Holds a blank line provisionally inside the open indented code block. It is incorporated into the
block if a later indented line continues the block; otherwise, it is discarded when the block
closes.
-/
def indentedCodeAddBlank (z : BlockZipper) (range : Syntax.Range) (rendered : String) :
    BlockZipper :=
  match z.openLeaf? with
  | some (.indentedCode lines pendingBlanks) =>
    { z with openLeaf? := some (.indentedCode lines (pendingBlanks.push (range, rendered))) }
  | _ => z

/-- Converts a frame into a finalized block. -/
def frameToBlock (frame : ZipperFrame) : Block Syntax.Range :=
  match frame.container with
  | .blockquote markers => .blockquote markers frame.closedChildren
  | .list kind => .list kind (!frame.loose) frame.closedChildren
  | .listItem marker _ => .listItem marker frame.closedChildren

/--
Pops the deepest container, finalizes it as a `Block`, and attaches it as a child
of its parent. This is a no-op when only the document root is open.
-/
def closeContainer (z : BlockZipper) : BlockZipper :=
  let z := z.closeLeaf
  match z.spine.back? with
  | none => z
  | some frame =>
    let z := { z with spine := z.spine.pop }
    z.pushChild (frameToBlock frame)

/-- Closes every container down to the document root and returns its children. -/
def finalize (z : BlockZipper) : Array (Block Syntax.Range) := Id.run do
  let mut z := z.closeLeaf
  while !z.spine.isEmpty do
    z := z.closeContainer
  return z.documentChildren
