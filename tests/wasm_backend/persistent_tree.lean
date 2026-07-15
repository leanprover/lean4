module

public meta import PersistentTree

/-!
Tests version branching and node identity in the persistent-tree UI model.
-/

open PersistentTree

#eval do
  let v0 := initial
  let v1 := insert v0 4
  let v2 := insert v1 12
  let branch := insert (select v2 1) 6
  IO.println s!"versions={branch.versions.size} selected={branch.selected} parent={(selectedVersion branch).parent}"
  IO.println s!"sizes={size (selectedVersion v0).root},{size (selectedVersion v1).root},{size (selectedVersion v2).root},{size (selectedVersion branch).root}"
  IO.println s!"shared-left={leftRootId (selectedVersion v1).root == leftRootId (selectedVersion v2).root}"
  IO.println s!"branch-shared-right={rightRootId (selectedVersion v1).root == rightRootId (selectedVersion branch).root}"
  IO.println s!"fresh-roots={rootId (selectedVersion v1).root != rootId (selectedVersion v2).root && rootId (selectedVersion v2).root != rootId (selectedVersion branch).root}"
