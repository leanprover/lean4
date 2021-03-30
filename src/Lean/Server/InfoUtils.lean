/-
Copyright (c) 2021 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.DocString
import Lean.Elab.InfoTree
import Lean.Util.Sorry

namespace Lean.Elab

/--
  For every branch, find the deepest node in that branch matching `p`
  with a surrounding context (the innermost one) and return all of them. -/
partial def InfoTree.deepestNodes (p : Info → Bool) : InfoTree → List (ContextInfo × Info) :=
  go none
where go ctx?
  | context ctx t => go ctx t
  | n@(node i cs) =>
    let cs := cs.toList
    let ccs := cs.map (go ctx?)
    let cs := ccs.join
    if !cs.isEmpty then cs
    else match ctx?, p i with
      | some ctx, true => [(ctx, i)]
      | _,        _    => []
  | _ => []

def Info.stx : Info → Syntax
  | ofTacticInfo i         => i.stx
  | ofTermInfo i           => i.stx
  | ofCommandInfo i        => i.stx
  | ofMacroExpansionInfo i => i.before
  | ofFieldInfo i          => i.stx

def Info.pos? (i : Info) : Option String.Pos :=
  i.stx.getPos? (originalOnly := true)

def Info.tailPos? (i : Info) : Option String.Pos :=
  i.stx.getTailPos? (originalOnly := true)

def InfoTree.smallestInfo? (p : Info → Bool) (t : InfoTree) : Option (ContextInfo × Info) :=
  let ts := t.deepestNodes p

  let infos := ts.map fun (ci, i) =>
    let diff := i.tailPos?.get! - i.pos?.get!
    (diff, ci, i)

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
partial def InfoTree.smallestTacticStates (t : InfoTree) : Array (String.Pos × ContextInfo × TacticInfo) :=
  let ts := tacticLeaves t
  let ts := ts.filterMap fun
    | (ci, i@(Info.ofTacticInfo ti)) => some (i.pos?.get!, ci, ti)
    | _ => none
  ts.toArray.qsort fun a b => a.1 < b.1
where tacticLeaves t :=
  t.deepestNodes fun
    | i@(Info.ofTacticInfo _) => i.pos?.isSome ∧ i.tailPos?.isSome
    | _ => false

structure GoalsAtResult where
  ctxInfo    : ContextInfo
  tacticInfo : TacticInfo
  useAfter   : Bool

partial def InfoTree.goalsAt? (t : InfoTree) (hoverPos : String.Pos) : Option GoalsAtResult := do
  let ts := t.smallestTacticStates
  for i in [:ts.size] do
    let (pos, ctxInfo, tacticInfo) := ts[i]
    let endPos := tacticInfo.stx.getTailPos?.get!
    if i == ts.size - 1 then
      let trailSize := tacticInfo.stx.getTrailingSize
      if pos <= hoverPos && hoverPos <= endPos + trailSize then
        return some { ctxInfo := ctxInfo, tacticInfo := tacticInfo, useAfter := hoverPos >= endPos }
    else
      let (nextPos, _, _) := ts[i+1]
      if pos <= hoverPos && hoverPos < nextPos then
        return some { ctxInfo := ctxInfo, tacticInfo := tacticInfo, useAfter := hoverPos >= endPos }
  return none

end Lean.Elab
