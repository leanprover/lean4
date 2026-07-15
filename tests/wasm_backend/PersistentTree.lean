module

/-!
Pure model for the browser persistent-tree demo.
-/

namespace PersistentTree

public inductive Tree where
  | empty
  | node (id key : UInt32) (left right : Tree)
  deriving Inhabited

public structure Version where
  id : UInt32
  parent : Option UInt32
  inserted : Option UInt32
  root : Tree
  deriving Inhabited

public structure Model where
  versions : Array Version
  selected : UInt32
  nextNodeId : UInt32
  nextVersionId : UInt32
  deriving Inhabited

private def insertTree (key nextId : UInt32) (tree : @& Tree) : Tree × UInt32 × Bool :=
  match tree with
  | .empty => (.node nextId key .empty .empty, nextId + 1, true)
  | old@(.node _ oldKey left right) =>
    if key == oldKey then (old, nextId, false)
    else if key < oldKey then
      let (left', nextId, changed) := insertTree key nextId left
      if changed then (.node nextId oldKey left' right, nextId + 1, true) else (old, nextId, false)
    else
      let (right', nextId, changed) := insertTree key nextId right
      if changed then (.node nextId oldKey left right', nextId + 1, true) else (old, nextId, false)

public def initial : Model :=
  let (root, nextNodeId, _) := insertTree 8 1 .empty
  { versions := #[{ id := 0, parent := none, inserted := some 8, root }]
    selected := 0, nextNodeId, nextVersionId := 1 }

public def selectedVersion (m : @& Model) : Version :=
  m.versions.getD m.selected.toNat default

public def select (m : @& Model) (index : UInt32) : Model :=
  if index.toNat < m.versions.size then { m with selected := index } else m

private def contains (key : UInt32) (tree : @& Tree) : Bool :=
  match tree with
  | .empty => false
  | .node _ oldKey left right =>
    if key == oldKey then true else if key < oldKey then contains key left else contains key right

public def hasKey (m : @& Model) (key : UInt32) : Bool :=
  contains key (selectedVersion m).root

public def insert (m : @& Model) (key : UInt32) : Model :=
  let base := selectedVersion m
  if hasKey m key then
    { versions := m.versions, selected := m.selected, nextNodeId := m.nextNodeId,
      nextVersionId := m.nextVersionId }
  else
    let (root, nextNodeId, _) := insertTree key m.nextNodeId base.root
    let version : Version :=
      { id := m.nextVersionId, parent := some base.id, inserted := some key, root }
    { versions := m.versions.push version
      selected := m.versions.size.toUInt32
      nextNodeId
      nextVersionId := m.nextVersionId + 1 }

public def rootId : Tree → UInt32
  | .empty => 0
  | .node id _ _ _ => id

public def leftRootId : Tree → UInt32
  | .empty => 0
  | .node _ _ left _ => rootId left

public def rightRootId : Tree → UInt32
  | .empty => 0
  | .node _ _ _ right => rootId right

public def size : Tree → Nat
  | .empty => 0
  | .node _ _ left right => 1 + size left + size right

end PersistentTree
