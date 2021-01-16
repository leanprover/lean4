/-
Copyright (c) 2021 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Elab.InfoTree

namespace Lean.Elab

/-- Find the deepest node matching `p` in the first subtree which contains a matching node.
The result is wrapped in all outer `ContextInfo`s. -/
partial def InfoTree.smallestNode? (p : Info → Bool) : InfoTree → Option InfoTree
  | context i t => context i <$> t.smallestNode? p
  | n@(node i cs) =>
    let cs := cs.map (·.smallestNode? p)
    let cs := cs.filter (·.isSome)
    if !cs.isEmpty then cs.get! 0
    else if p i then some n
    else none
  | _ => none

/-- For every branch, find the deepest node in that branch matching `p`
and return all of them. Each result is wrapper in all outer `ContextInfo`s. -/
partial def InfoTree.smallestNodes (p : Info → Bool) : InfoTree → List InfoTree
  | context i t => t.smallestNodes p |>.map (context i)
  | n@(node i cs) =>
    let cs := cs.toList
    let ccs := cs.map (smallestNodes p)
    let cs := ccs.join
    if !cs.isEmpty then cs
    else if p i then [n]
    else []
  | _ => []

def TermInfo.pos? (i : TermInfo) : Option String.Pos :=
  i.stx.getPos

def TermInfo.tailPos? (i : TermInfo) : Option String.Pos :=
  i.stx.getTailPos

def TacticInfo.pos? (i : TacticInfo) : Option String.Pos :=
  i.stx.getPos

def TacticInfo.tailPos? (i : TacticInfo) : Option String.Pos :=
  i.stx.getTailPos

end Lean.Elab
