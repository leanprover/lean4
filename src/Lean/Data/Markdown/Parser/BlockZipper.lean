/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
import Init
public import Lean.Data.Markdown.Block
public import Lean.Data.Markdown.Parser.Html
public import Lean.Data.Markdown.Parser.Children
import Lean.Data.Markdown.InlineSource

namespace Lean.Markdown


/-!
# The In-Progress Zipper

While identifying the block structure of a document, lines are checked one at a time and added in
order. A zipper-like structure makes it easy to see the surrounding block context and to modify it
at the right-hand edge.
-/

/--
A container that is currently open and may still receive child blocks.
-/
public inductive OpenContainer (s : String.Slice) where
  /--
  A blockquote. `markers` accumulates the `>` markers from
  every continuation line that has been seen so far.
  -/
  | blockquote (markers : Array s.Subslice)
  /--
  A list item that is open, which makes it the last item of its list so far.
  * `list` is the list that the item belongs to, with the items that closed before this one.
  * `marker` is this item's bullet or ordered marker.
  * `contentColumn` is the column at which the item's content begins. Subsequent lines must be
    indented to at least this column to count as continuations of this item (CommonMark §5.2).
  -/
  | listItem (list : OpenList s) (marker : s.Subslice) (contentColumn : Columns)
deriving Inhabited

/--
A frame of the zipper's spine, which is an open container plus the children that have already been
closed inside it, in source order.
-/
public structure ZipperFrame (s : String.Slice) where
  /--
  The container in this frame. Subsequent frames in the stack represent the last child of this open
  container.
  -/
  container : OpenContainer s
  /-- The children that have already been closed inside this frame's container. -/
  children : Children s := {}
deriving Inhabited

/-- A leaf block that is currently open and may still accept additional source lines. -/
public inductive OpenLeaf (s : String.Slice) where
  /--
  An open paragraph that is being extended line by line. Closing the paragraph (because of a blank
  line, a new block opener, or the parent container closing) finalizes it as `Block.Raw.paragraph`.
  -/
  | paragraph (lines : Lines s)
  /--
  An open fenced code block. `lines` accumulates content lines until either a matching closing fence
  appears (yielding `Block.Raw.fencedCode` with `closeFence? := some _`) or the parent container
  closes at EOF (yielding `closeFence? := none`).
  -/
  | fencedCode (info : FenceInfo s) (openFence : s.Subslice) (lines : Array (VerbatimLine s))
  /--
  An open indented code block.

  - `lines` are the content lines that have been committed so far, after the four columns of
    indentation.
  - `pendingBlanks` records blank lines that may belong to this block. They are promoted to `lines`
    when a subsequent indented line continues the block, and discarded when an unindented non-blank
    line closes the block. This matches CommonMark's rule that blank lines between indented chunks
    are part of the code block, but blank lines that follow the final chunk are not.
  -/
  | indentedCode (lines : Array (VerbatimLine s)) (pendingBlanks : Array (VerbatimLine s))
  /--
  An open HTML block. `kind` selects the end condition, and `lines` accumulates the block's lines,
  starting with the one that met the start condition.
  -/
  | html (kind : HtmlBlockKind) (lines : Array (VerbatimLine s))
deriving Inhabited

/--
The block parsing state. Maintains the spine of currently-open containers plus an optional open leaf
at the bottom.

An empty spine means that only the document is open.

Invariants:
- If `openLeaf?` is `some _`, that leaf logically lives inside the deepest spine frame, or directly
  under the document if the spine is empty. Extending the leaf adds to its content, and closing the
  leaf pushes a `Block.Raw` onto that container's children.
- A list contains only list items. An `OpenList` has items and nothing else, and every open list is
  either the list of an item frame or the pending list of the container around it. `Children.push`,
  the one operation that appends a block, finishes the pending list first.
-/
public structure BlockZipper (s : String.Slice) where
  /-- The children of the document root. -/
  document : Children s := .empty
  /-- Open containers below the document root, deepest last. -/
  spine : Array (ZipperFrame s) := #[]
  /-- An open leaf node, if one is present. -/
  openLeaf? : Option (OpenLeaf s) := none
  /--
  The position in `spine` of the outermost list that the most recent blank line could still make
  loose (CommonMark §5.3), or `none` when there is no such list or the next block has begun. A list
  is at the position of its open item's frame, or one past the deepest frame when it is the pending
  list of the deepest container.

  A blank line makes a list loose when the next block begins in one of the list's items. The lists
  it could make loose are therefore the open lists around it, from this position inward. The
  outermost of them is inside the nearest enclosing blockquote, because a blank line inside a
  blockquote separates blocks of the blockquote, not blocks of a list that contains the blockquote.
  -/
  blankLineFloor? : Option Nat := none
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
  | .paragraph lines => .paragraph (.ofLines lines)
  | .fencedCode info openFence lines => .fencedCode info openFence none lines
  | .indentedCode lines _pendingBlanks => .indentedCode lines
  | .html _ lines => .html lines

/--
Applies `f` to the children of the deepest open container, which are the document's children when
there is no open container.
-/
@[inline] def modifyChildren (z : BlockZipper s) (f : Children s → Children s) : BlockZipper s :=
  if z.spine.isEmpty then
    { z with document := f z.document }
  else
    { z with
      spine :=
        z.spine.modify (z.spine.size - 1) fun frame => { frame with children := f frame.children } }

/--
Applies `f` to the children of the deepest open container, which are the document's children when
no container is open, and returns the value that `f` produces alongside the new children.
-/
@[inline] def modifyGetChildren (z : BlockZipper s) (f : Children s → Children s × α) :
    BlockZipper s × α :=
  if h : 0 < z.spine.size then
    let frame := z.spine.back h
    let spine := z.spine.pop
    let { container, children } := frame
    let (children, a) := f children
    ({ z with spine := spine.push { container, children } }, a)
  else
    let (document, a) := f z.document
    ({ z with document }, a)

/-- Adds a finished block as the last child of the deepest open container. -/
def pushChild (z : BlockZipper s) (b : Block.Raw s) : BlockZipper s :=
  z.modifyChildren (·.push b)

/-- Closes any open leaf, attaching it to the deepest container. -/
public def closeLeaf (z : BlockZipper s) : BlockZipper s :=
  match z.openLeaf? with
  | none => z
  | some leaf =>
    let z := z.pushChild (leafToBlock leaf)
    { z with openLeaf? := none }

/--
The least spine index from which every deeper frame is a list item.

It is one past the deepest blockquote, or `0` when there is none.
-/
public def listLikeFloor (z : BlockZipper s) : Nat := Id.run do
  let mut i := z.spine.size
  while i > 0 do
    i := i - 1
    if let some { container := .blockquote .., .. } := z.spine[i]? then return i + 1
  return 0

/--
Records a blank line in the deepest open container.

A blank line between two blocks of a list item, or between two items, makes the list loose
(CommonMark §5.3). Which list that is depends on where the next block begins, so the blank line is
remembered until then, along with the outermost list it could affect. A blank line inside a
blockquote affects only the blockquote's own content.
-/
public def recordBlankLine (z : BlockZipper s) : BlockZipper s :=
  let topIsListLike :=
    match z.spine.back? with
    | some frame =>
      (match frame.container with | .listItem .. => true | _ => false) ||
        frame.children.pendingList?.isSome
    | none => z.document.pendingList?.isSome
  { z with blankLineFloor? := if topIsListLike then some z.listLikeFloor else none }

/--
Records a line that continues the open block. Any blank line before it was inside that block
instead of between two blocks, so it doesn't make any list loose.
-/
public def recordContentLine (z : BlockZipper s) : BlockZipper s :=
  { z with blankLineFloor? := none }

/--
Marks the list of the deepest open container as loose (CommonMark §5.3) when that container is a
list item at spine index `floor` or deeper.
-/
def markLooseAbove (z : BlockZipper s) (floor : Nat) : BlockZipper s :=
  let top := z.spine.size - 1
  if z.spine.isEmpty || top < floor then z
  else
    { z with
      spine := z.spine.modify top fun
        | { container := .listItem list marker contentColumn, children } =>
          { container := .listItem { list with loose := true } marker contentColumn, children }
        | frame => frame }

/--
Records that a block begins as a child of the deepest open container. A blank line since the
container's previous block makes its list loose.
-/
def startBlock (z : BlockZipper s) : BlockZipper s :=
  match z.blankLineFloor? with
  | some floor => { z.markLooseAbove floor with blankLineFloor? := none }
  | none => z

/--
Closes the deepest container. A blockquote becomes the last child of the container around it. A
list item is added to its list, which becomes the pending list of the container around it, since
the next line may add another item. Does nothing when only the document is open.
-/
public def closeContainer (z : BlockZipper s) : BlockZipper s :=
  let z := z.closeLeaf
  if h : 0 < z.spine.size then
    let frame := z.spine.back h
    let z := { z with spine := z.spine.pop }
    let { container, children } := frame
    let children := children.flushLists
    match container with
    | .blockquote markers => z.pushChild (.blockquote markers children.blocks)
    | .listItem list marker _ =>
      let list := { list with items := list.items.push { marker, children := children.blocks } }
      z.modifyChildren (·.setPendingList list)
  else z

/--
Opens a blockquote as the last child of the deepest open container, closing any open leaf first.
-/
public def openBlockquote (z : BlockZipper s) (markers : Array s.Subslice) : BlockZipper s :=
  let z := z.closeLeaf.startBlock
  { z with spine := z.spine.push { container := .blockquote markers } }

/--
Opens a list item as the last child of the deepest open container, closing any open leaf first. The
item joins the container's pending list when that list is of the item's kind; otherwise the item
begins a new list. A blank line before the item makes the list that it joins loose.
-/
public def openItem (z : BlockZipper s) (kind : ListKind) (marker : s.Subslice)
    (contentColumn : Columns) : BlockZipper s :=
  let z := z.closeLeaf
  let (z, list?) := z.modifyGetChildren (·.takePendingList kind)
  match list? with
  | some list =>
    let z := { z with spine := z.spine.push { container := .listItem list marker contentColumn } }
    z.startBlock
  | none =>
    let z := z.startBlock
    { z with spine := z.spine.push { container := .listItem { kind } marker contentColumn } }

/-- Replaces the open leaf at the bottom of the spine, closing any prior one. -/
public def openLeaf (z : BlockZipper s) (l : OpenLeaf s) : BlockZipper s :=
  let z := z.closeLeaf.startBlock
  { z with openLeaf? := some l }

/--
Adds a finalized block as a child of the deepest open container, closing any open leaf first. Used
for blocks like ATX headings that don't go through `OpenLeaf`.
-/
public def addBlock (z : BlockZipper s) (b : Block.Raw s) : BlockZipper s :=
  z.closeLeaf.startBlock.pushChild b

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

/-- Appends a source line to the open paragraph, if any. Otherwise, does nothing. -/
public def extendParagraph (z : BlockZipper s) (line : s.Subslice) : BlockZipper s :=
  z.modifyLeaf fun
    | .paragraph lines => .paragraph (lines.push line)
    | leaf => leaf

/-- Appends a verbatim line to the open fenced code block, if any. Otherwise, does nothing. -/
public def extendFencedCode (z : BlockZipper s) (line : VerbatimLine s) : BlockZipper s :=
  z.modifyLeaf fun
    | .fencedCode info openFence lines => .fencedCode info openFence (lines.push line)
    | leaf => leaf

/-- Appends a verbatim line to the open HTML block, if any. Otherwise, does nothing. -/
public def extendHtml (z : BlockZipper s) (line : VerbatimLine s) : BlockZipper s :=
  z.modifyLeaf fun
    | .html kind lines => .html kind (lines.push line)
    | leaf => leaf

/-- Closes the open fenced code block with a matching closing fence. -/
public def closeFencedCode (z : BlockZipper s) (closeFence : s.Subslice) : BlockZipper s :=
  match z.openLeaf? with
  | some (.fencedCode info openFence lines) =>
    let z := z.pushChild (.fencedCode info openFence (some closeFence) lines)
    { z with openLeaf? := none }
  | _ => z

/--
Appends an indented content line to the open indented code block. Any pending blanks that were
recorded since the last content line are promoted to real content lines first.
-/
public def indentedCodeAddLine (z : BlockZipper s) (line : VerbatimLine s) : BlockZipper s :=
  z.modifyLeaf fun
    | .indentedCode lines pendingBlanks => .indentedCode (lines ++ pendingBlanks |>.push line) #[]
    | leaf => leaf

/--
Records a blank line provisionally inside the open indented code block. It is incorporated into the
block if a later indented line continues the block; otherwise, it is discarded when the block
closes.
-/
public def indentedCodeAddBlank (z : BlockZipper s) (line : VerbatimLine s) : BlockZipper s :=
  z.modifyLeaf fun
    | .indentedCode lines pendingBlanks => .indentedCode lines (pendingBlanks.push line)
    | leaf => leaf

/--
Appends `m` to the markers of the blockquote frame at spine index `i`. A frame of another kind is
left as it is.
-/
public def pushBlockquoteMarker (z : BlockZipper s) (i : Nat) (m : s.Subslice) : BlockZipper s :=
  { z with
    spine := z.spine.modify i fun
      | { container := .blockquote markers, children } =>
        { container := .blockquote (markers.push m), children }
      | frame => frame }

@[simp] public theorem spine_size_pushBlockquoteMarker (z : BlockZipper s) (i : Nat)
    (m : s.Subslice) : (z.pushBlockquoteMarker i m).spine.size = z.spine.size := by
  simp [pushBlockquoteMarker]

/-- Closes every container down to the document root and returns its children. -/
public def finalize (z : BlockZipper s) : Array (Block.Raw s) := Id.run do
  let mut z := z.closeLeaf
  while !z.spine.isEmpty do
    z := z.closeContainer
  return z.document.flushLists.blocks
