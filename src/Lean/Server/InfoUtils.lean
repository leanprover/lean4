/-
Copyright (c) 2021 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.DocString
import Lean.Elab.InfoTree
import Lean.Util.Sorry

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
and return all of them. Each result is wrapped in all outer `ContextInfo`s. -/
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

def Info.stx : Info → Syntax
  | ofTacticInfo i         => i.stx
  | ofTermInfo i           => i.stx
  | ofMacroExpansionInfo i => i.before
  | ofFieldInfo i          => i.stx

def Info.pos? (i : Info) : Option String.Pos :=
  i.stx.getPos? (originalOnly := true)

def Info.tailPos? (i : Info) : Option String.Pos :=
  i.stx.getTailPos? (originalOnly := true)

def InfoTree.smallestInfo? (p : Info → Bool) (t : InfoTree) : Option (ContextInfo × Info) :=
  let ts := t.smallestNodes p

  let infos : List (Nat × ContextInfo × Info) := ts.filterMap fun
    | context ci (node i _) =>
      let diff := i.tailPos?.get! - i.pos?.get!
      some (diff, ci, i)
    | _ => none

  infos.toArray.getMax? (fun a b => a.1 > b.1) |>.map fun (_, ci, i) => (ci, i)

/-- Find an info node, if any, which should be shown on hover/cursor at position `hoverPos`. -/
partial def InfoTree.hoverableInfoAt? (t : InfoTree) (hoverPos : String.Pos) : Option (ContextInfo × Info) :=
  t.smallestInfo? fun i =>
    if let (some pos, some tailPos) := (i.pos?, i.tailPos?) then
      if pos ≤ hoverPos ∧ hoverPos < tailPos then
        match i with
        | Info.ofTermInfo ti =>
          !ti.expr.isSyntheticSorry &&
          -- TODO: see if we can get rid of this
          #[identKind,
            strLitKind,
            charLitKind,
            numLitKind,
            scientificLitKind,
            nameLitKind,
            fieldIdxKind,
            interpolatedStrLitKind,
            interpolatedStrKind
          ].contains i.stx.getKind
        | Info.ofFieldInfo _ => true
        | _ => false
      else false
    else false

/-- Construct a hover popup, if any, from an info node in a context.-/
def Info.fmtHover? (ci : ContextInfo) (i : Info) : IO (Option Format) := do
  let lctx ← match i with
    | Info.ofTermInfo i  => i.lctx
    | Info.ofFieldInfo i => i.lctx
    | _                  => return none

  ci.runMetaM lctx do
    match i with
    | Info.ofTermInfo ti =>
      let tp ← Meta.inferType ti.expr
      let eFmt ← Meta.ppExpr ti.expr
      let tpFmt ← Meta.ppExpr tp
      let hoverFmt := f!"```lean
{eFmt} : {tpFmt}
```"
      if let some n := ti.expr.constName? then
        if let some doc ← findDocString? n then
          return f!"{hoverFmt}\n***\n{doc}"
      return hoverFmt

    | Info.ofFieldInfo fi =>
      let tp ← Meta.inferType fi.val
      let tpFmt ← Meta.ppExpr tp
      return f!"```lean
{fi.name} : {tpFmt}
```"

    | _ => return none

/-- Return a flattened list of smallest-in-span tactic info nodes, sorted by position. -/
partial def InfoTree.smallestTacticStates (t : InfoTree) : Array (Nat × ContextInfo × TacticInfo) :=
  let ts := tacticLeaves t
  let ts := ts.filterMap fun
    | context ci (node i@(Info.ofTacticInfo ti) _) => some (i.pos?.get!, ci, ti)
    | _ => none
  ts.toArray.qsort fun a b => a.1 < b.1

  where tacticLeaves (t : InfoTree) : List InfoTree :=
          t.smallestNodes fun
            | i@(Info.ofTacticInfo _) => i.pos?.isSome ∧ i.tailPos?.isSome
            | _ => false

partial def InfoTree.goalsAt? (t : InfoTree) (hoverPos : String.Pos) : Option (ContextInfo × TacticInfo) :=
  let ts := t.smallestTacticStates
  -- The extent of a tactic state is (pos, pos of next tactic)
  let extents := ts.mapIdx fun i (p, _, ti) =>
    (p, if h : (i.val+1) < ts.size then
          ts.get ⟨i.val+1, h⟩ |>.1
        else
          ti.stx.getTailPos?.get!)
  let idx? := extents.findIdx? fun (p, tp) => p ≤ hoverPos ∧ hoverPos < tp
  idx?.map fun idx => ts.get! idx |> fun (_, ci, ti) => (ci, ti)

end Lean.Elab
