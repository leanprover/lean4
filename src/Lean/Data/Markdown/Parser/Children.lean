/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
import Init
public import Lean.Data.Markdown.Block

namespace Lean.Markdown

/-!
# Container Children

The children of a container while the block structure is being parsed. A list whose last item has
closed may still receive another item, so it is kept apart from the finished blocks until the next
line, which determines whether it continues. The constructor of `Children` is private to protect
invariants. Because `push` is the only operation that appends a block, and it finishes the pending
list first, a block never ends up before the list that precedes it.
-/

/-- A list item that has been closed inside its list. -/
public structure ClosedItem (s : String.Slice) where
  /-- The item's bullet or ordered marker. -/
  marker : s.Subslice
  /-- The item's blocks, in source order. -/
  children : Array (Block.Raw s)

/--
A list that may still receive items.
-/
public structure OpenList (s : String.Slice) where
  /-- The kind of the list. -/
  kind : ListKind
  /--
  Whether a blank line has been encountered between two blocks of the list, which makes it loose
  (CommonMark §5.3).
  -/
  loose : Bool := false
  /-- The items that have been closed, in source order. -/
  items : Array (ClosedItem s) := #[]

/--
The closed children of a container, in source order.

When a list item closes, its list is not finished. The next line that begins with a marker of the
same kind adds another item to it. While still open, the list is saved in `pendingList?`. It becomes
the last element of `blocks` when closed.
-/
public structure Children (s : String.Slice) where
  private mk ::
  /-- The finished blocks. -/
  blocks : Array (Block.Raw s)
  /-- The list that is the last child so far and may still receive another item. -/
  pendingList? : Option (OpenList s)

namespace Children

variable {s : String.Slice}

/-- No children. -/
public def empty : Children s := { blocks := #[], pendingList? := none }

public instance : EmptyCollection (Children s) where
  emptyCollection := empty

public instance : Inhabited (Children s) := ⟨empty⟩

/-- Finishes the pending list, if there is one, as the last block. -/
public def flushLists (c : Children s) : Children s :=
  match c with
  | { blocks, pendingList? := some list } =>
    let items := list.items.map fun item => Block.Raw.listItem item.marker item.children
    { blocks := blocks.push (.list list.kind (!list.loose) items), pendingList? := none }
  | c => c

/-- Adds `b` after the children so far. Any pending lists are closed first. -/
public def push (c : Children s) (b : Block.Raw s) : Children s :=
  let c := c.flushLists
  { c with blocks := c.blocks.push b }

/--
Makes `list` the pending list. A list that was pending before is finished first, as the last block.
-/
public def setPendingList (c : Children s) (list : OpenList s) : Children s :=
  { c.flushLists with pendingList? := some list }

/-- Removes and returns the pending list when it is a list of `kind`. -/
public def takePendingList (c : Children s) (kind : ListKind) : Children s × Option (OpenList s) :=
  match c with
  | { blocks, pendingList? := some list } =>
    if list.kind.sameKind kind then ({ blocks, pendingList? := none }, some list)
    else ({ blocks, pendingList? := some list }, none)
  | c => (c, none)

/-- Whether there are no children. -/
public def isEmpty (c : Children s) : Bool := c.blocks.isEmpty && c.pendingList?.isNone
