/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
import Init
public import Lean.Data.Markdown.Basic

namespace Lean.Markdown


/-!
## The In-Progress Zipper

While identifying the block structure of a document, lines are checked one at a time and added in
order. A zipper-like structure makes it easy to see the surrounding block context and to modify it
at the right-hand edge.
-/

/--
A container that is currently open and may still receive child blocks.
-/
public inductive OpenContainer (s : String.Slice) where
  /--
  A blockquote. `markers` accumulates the ranges of `>` markers from
  every continuation line that has been seen so far.
  -/
  | blockquote (markers : Array s.Subslice)
  /-- A list. -/
  | list (kind : ListKind)
  /--
  A list item.

  - `marker` is the range of this item's bullet or ordered marker.
  - `contentColumn` is the column at which the item's content begins;
    subsequent lines must be indented to at least this column to count as
    continuations of this item (CommonMark §5.2).
  -/
  | listItem (marker : s.Subslice) (contentColumn : Nat)
deriving Inhabited

/--
A frame of the zipper's spine: an open container plus the children that have
already been closed inside it, in source order.
-/
public structure ZipperFrame (s : String.Slice) where
  /--
  The container in this frame. Subsequent frames in the stack represent the last child of this open
  container.
  -/
  container : OpenContainer s
  /--
  Children that have already been closed inside this frame's container.
  -/
  closedChildren : Array (Block.Raw s) := #[]
  /--
  For list frames: set when a blank line followed by more content in this list has been observed
  during parsing.
  -/
  loose : Bool := false
deriving Inhabited

/-- A leaf block that is currently open and may still accept additional source lines. -/
public inductive OpenLeaf (s : String.Slice) where
  /--
  An open paragraph being extended line by line. Closing the paragraph (because of a blank line, a
  new block opener, or the parent container closing) finalizes it as `Block.Raw.paragraph`.
  -/
  | paragraph (lines : Array s.Subslice)
  /--
  An open fenced code block. `lines` accumulates content lines until either a matching closing fence
  appears (yielding `Block.Raw.fencedCode` with `closeFence? := some _`) or the parent container
  closes at EOF (yielding `closeFence? := none`).
  -/
  | fencedCode (info : FenceInfo s) (openFence : s.Subslice) (lines : Array s.Subslice)
  /--
  An open indented code block.

  - `lines` are the content lines committed so far. Each element is a pair of the line's source
    range after the 4 cols of indent that defined the code block (relative to the parent container's
    content column) and the rendered string, in which any partial tab at that point is materialized
    per CommonMark §2.2.
  - `pendingBlanks` records blank lines that may belong to this block: they are promoted to `lines`
    when a subsequent indented line continues the block, and discarded when an unindented non-blank
    line closes the block. This matches CommonMark's rule that blank lines between indented chunks
    are part of the code block, but blank lines following the final chunk are not.
  -/
  | indentedCode (lines : Array (s.Subslice × String))
      (pendingBlanks : Array (s.Subslice × String))
deriving Inhabited

/--
The block parsing state. Maintains the spine of currently-open containers
plus an optional open leaf at the bottom.

An empty spine means that only the document is open.

Invariants (preserved by the zipper operations below):
- If `openLeaf?` is `some _`, that leaf logically lives inside the deepest
  spine frame, or directly under the document if the spine is empty;
  extending the leaf adds to its content, and closing the leaf pushes a
  `Block.Raw` onto that container's children.
- A `OpenContainer.list` frame's immediate spine successor (when present) is
  always an `OpenContainer.listItem`.
-/
public structure BlockZipper (s : String.Slice) where
  /-- Closed children of the document root, in source order. -/
  documentChildren : Array (Block.Raw s) := #[]
  /-- Open containers below the document root, deepest last. -/
  spine : Array (ZipperFrame s) := #[]
  /-- An open leaf node, if one is present. -/
  openLeaf? : Option (OpenLeaf s) := none
  /--
  Whether the previous source line was blank (after consuming the current open containers'
  prefixes). Used to mark enclosing lists as loose when a blank line is followed by content that
  continues the list (CommonMark §5.3).
  -/
  lastWasBlank : Bool := false
deriving Inhabited

namespace BlockZipper

variable {s : String.Slice}

/-- A zipper with only the document root open, no children, and no open leaf. -/
public def empty : BlockZipper s := {}

/-- The deepest currently-open container, or `none` if only the document is open. -/
public def top? (z : BlockZipper s) : Option (OpenContainer s) :=
  z.spine.back?.map (·.container)

/--
Converts an open leaf into its closed `Block.Raw` form. Fenced code blocks are not terminated with a
fence.
-/
public def leafToBlock : OpenLeaf s → Block.Raw s
  | .paragraph lines => .paragraph lines
  | .fencedCode info openFence lines => .fencedCode info openFence none lines
  | .indentedCode lines _pendingBlanks => .indentedCode lines

/--
Pushes a finalized block onto the deepest spine frame's `closedChildren`, or directly onto
`documentChildren` if the spine is empty.
-/
def pushChild (z : BlockZipper s) (b : Block.Raw s) : BlockZipper s :=
  if z.spine.isEmpty then
    { z with documentChildren := z.documentChildren.push b }
  else
    { z with
      spine :=
        z.spine.modify (z.spine.size - 1)
          (fun frame => { frame with closedChildren := frame.closedChildren.push b }) }

/-- Closes any open leaf, attaching it to the deepest container. -/
public def closeLeaf (z : BlockZipper s) : BlockZipper s :=
  match z.openLeaf? with
  | none => z
  | some leaf =>
    let z := z.pushChild (leafToBlock leaf)
    { z with openLeaf? := none }

/-- Pushes a new container onto the spine, closing any open leaf first. -/
public def openContainer (z : BlockZipper s) (c : OpenContainer s) : BlockZipper s :=
  let z := z.closeLeaf
  { z with spine := z.spine.push { container := c } }

/-- Replaces the open leaf at the bottom of the spine, closing any prior one. -/
public def openLeaf (z : BlockZipper s) (l : OpenLeaf s) : BlockZipper s :=
  let z := z.closeLeaf
  { z with openLeaf? := some l }

/--
Adds a finalized block as a child of the deepest open container, closing any open leaf first. Used
for blocks like ATX headings that don't go through `OpenLeaf`.
-/
public def addBlock (z : BlockZipper s) (b : Block.Raw s) : BlockZipper s :=
  z.closeLeaf.pushChild b

/--
Replaces the open leaf with the result of `f`, applied to the current leaf. The leaf is taken out of
the zipper before `f` runs, so that `f` can extend the leaf's arrays without copying them.
-/
@[inline] def modifyLeaf (z : BlockZipper s) (f : OpenLeaf s → OpenLeaf s) : BlockZipper s :=
  match z.openLeaf? with
  | none => z
  | some leaf =>
    let z := { z with openLeaf? := none }
    { z with openLeaf? := some (f leaf) }

/-- Appends a source line to the open paragraph, if any. No-op otherwise. -/
public def extendParagraph (z : BlockZipper s) (line : s.Subslice) : BlockZipper s :=
  z.modifyLeaf fun
    | .paragraph lines => .paragraph (lines.push line)
    | leaf => leaf

/-- Appends a verbatim line to the open fenced code block, if any. No-op otherwise. -/
public def extendFencedCode (z : BlockZipper s) (line : s.Subslice) : BlockZipper s :=
  z.modifyLeaf fun
    | .fencedCode info openFence lines => .fencedCode info openFence (lines.push line)
    | leaf => leaf

/-- Closes the open fenced code block with a matching closing fence. -/
public def closeFencedCode (z : BlockZipper s) (closeFence : s.Subslice) : BlockZipper s :=
  match z.openLeaf? with
  | some (.fencedCode info openFence lines) =>
    let z := z.pushChild (.fencedCode info openFence (some closeFence) lines)
    { z with openLeaf? := none }
  | _ => z

/--
Appends an indented content line to the open indented code block. Any pending blanks recorded since
the last content line are promoted to real content lines first.
-/
public def indentedCodeAddLine (z : BlockZipper s) (range : s.Subslice) (rendered : String) :
    BlockZipper s :=
  z.modifyLeaf fun
    | .indentedCode lines pendingBlanks => .indentedCode (lines ++ pendingBlanks |>.push (range, rendered)) #[]
    | leaf => leaf

/--
Records a blank line provisionally inside the open indented code block. It is incorporated into the
block if a later indented line continues the block; otherwise, it is discarded when the block
closes.
-/
public def indentedCodeAddBlank (z : BlockZipper s) (range : s.Subslice) (rendered : String) :
    BlockZipper s :=
  z.modifyLeaf fun
    | .indentedCode lines pendingBlanks => .indentedCode lines (pendingBlanks.push (range, rendered))
    | leaf => leaf

/-- Converts a frame into a finalized block. -/
public def frameToBlock (frame : ZipperFrame s) : Block.Raw s :=
  match frame.container with
  | .blockquote markers => .blockquote markers frame.closedChildren
  | .list kind => .list kind (!frame.loose) frame.closedChildren
  | .listItem marker _ => .listItem marker frame.closedChildren

/--
Pops the deepest container, finalizes it as a `Block.Raw`, and attaches it as a child
of its parent. This is a no-op when only the document root is open.
-/
public def closeContainer (z : BlockZipper s) : BlockZipper s :=
  let z := z.closeLeaf
  match z.spine.back? with
  | none => z
  | some frame =>
    let z := { z with spine := z.spine.pop }
    z.pushChild (frameToBlock frame)

/-- Closes every container down to the document root and returns its children. -/
public def finalize (z : BlockZipper s) : Array (Block.Raw s) := Id.run do
  let mut z := z.closeLeaf
  while !z.spine.isEmpty do
    z := z.closeContainer
  return z.documentChildren
