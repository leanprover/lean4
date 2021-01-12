import Lean.Elab

namespace Lean.Elab

/-- Finds the smallest node matching `p` in the first subtree which contains a matching node.
Wraps the result in all outer `ContextInfo`s. -/
partial def InfoTree.smallestNode? (p : Info → Bool) : InfoTree → Option InfoTree
  | context i t => context i <$> t.smallestNode? p
  | n@(node i cs) =>
    let cs := cs.map (fun c => c.smallestNode? p)
    let cs := cs.filter (fun c? => c?.isSome)
    if !cs.isEmpty then cs.get! 0
    else if p i then some n
    else none
  | _ => none

/-- Finds the smallest node matching `p` in the first subtree which contains a matching node.
Wraps the result in all outer `ContextInfo`s. -/
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

def TermInfo.endPos? (i : TermInfo) : Option String.Pos :=
  i.stx.getTailPos

end Lean.Elab
