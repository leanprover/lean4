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
partial def InfoTree.deepestNodes (p : ContextInfo → Info → Std.PersistentArray InfoTree → Option α) : InfoTree → List α :=
  go none
where go ctx?
  | context ctx t => go ctx t
  | n@(node i cs) =>
    let ccs := cs.toList.map (go <| i.updateContext? ctx?)
    let cs' := ccs.join
    if !cs'.isEmpty then cs'
    else match ctx? with
      | some ctx => match p ctx i cs with
        | some a => [a]
        | _      => []
      | _        => []
  | _ => []

partial def InfoTree.foldInfo (f : ContextInfo → Info → α → α) (init : α) : InfoTree → α :=
  go none init
where go ctx? a
  | context ctx t => go ctx a t
  | node i ts =>
    let a := match ctx? with
      | none => a
      | some ctx => f ctx i a
    ts.foldl (init := a) (go <| i.updateContext? ctx?)
  | _ => a

def Info.isTerm : Info → Bool
  | ofTermInfo _ => true
  | _ => false

def Info.isCompletion : Info → Bool
  | ofCompletionInfo .. => true
  | _ => false

def InfoTree.getCompletionInfos (infoTree : InfoTree) : Array (ContextInfo × CompletionInfo) :=
  infoTree.foldInfo (init := #[]) fun ctx info result =>
    match info with
    | Info.ofCompletionInfo info => result.push (ctx, info)
    | _ => result

def Info.stx : Info → Syntax
  | ofTacticInfo i         => i.stx
  | ofTermInfo i           => i.stx
  | ofCommandInfo i        => i.stx
  | ofMacroExpansionInfo i => i.before
  | ofFieldInfo i          => i.stx
  | ofCompletionInfo i     => i.stx

def Info.pos? (i : Info) : Option String.Pos :=
  i.stx.getPos? (originalOnly := true)

def Info.tailPos? (i : Info) : Option String.Pos :=
  i.stx.getTailPos? (originalOnly := true)

def Info.size? (i : Info) : Option Nat := OptionM.run do
  let pos ← i.pos?
  let tailPos ← i.tailPos?
  return tailPos - pos

-- `Info` without position information are considered to have "infinite" size
def Info.isSmaller (i₁ i₂ : Info) : Bool :=
  match i₁.size?, i₂.pos? with
  | some sz₁, some sz₂ => sz₁ < sz₂
  | some _, none => true
  | _, _ => false

def Info.occursBefore? (i : Info) (hoverPos : String.Pos) : Option Nat := OptionM.run do
  let tailPos ← i.tailPos?
  guard (tailPos ≤ hoverPos)
  return hoverPos - tailPos

def InfoTree.smallestInfo? (p : Info → Bool) (t : InfoTree) : Option (ContextInfo × Info) :=
  let ts := t.deepestNodes fun ctx i _ => if p i then some (ctx, i) else none

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

structure GoalsAtResult where
  ctxInfo    : ContextInfo
  tacticInfo : TacticInfo
  useAfter   : Bool

/-
  Try to retrieve `TacticInfo` for `hoverPos`.
  We retrieve the `TacticInfo` `info`, if there is a node of the form `node (ofTacticInfo info) children` s.t.
  - `hoverPos` is sufficiently inside `info`'s range (see code), and
  - None of the `children` can provide satisfy the condition above. That is, for composite tactics such as
    `induction`, we always give preference for information stored in nested (children) tactics.

  Moreover, we instruct the LSP server to use the state after the tactic execution if hoverPos >= endPos *and*
  there is no nested tactic info (i.e. it is a leaf tactic; tactic combinators should decide for themselves
  where to show intermediate/final states)
-/
partial def InfoTree.goalsAt? (t : InfoTree) (hoverPos : String.Pos) : List GoalsAtResult := do
  t.deepestNodes fun
    | ctx, i@(Info.ofTacticInfo ti), cs => OptionM.run do
      let (some pos, some tailPos) ← pure (i.pos?, i.tailPos?)
        | failure
      let trailSize := i.stx.getTrailingSize
      -- NOTE: include position just after tactic, i.e. when the cursor is still adjacent
      -- (even when `trailSize == 0`, which is the case at EOF)
      guard <| pos ≤ hoverPos ∧ hoverPos < tailPos + Nat.max 1 trailSize
      return { ctxInfo := ctx, tacticInfo := ti, useAfter :=
        hoverPos > pos && !cs.any (hasNestedTactic pos tailPos) }
    | _, _, _ => none
where
  hasNestedTactic (pos tailPos) : InfoTree → Bool
    | InfoTree.node (Info.ofTacticInfo ti) cs => do
      if let `(by $t) := ti.stx then
        return false  -- ignore term-nested proofs such as in `simp [show p by ...]`
      if let (some pos', some tailPos') := (ti.stx.getPos?, ti.stx.getTailPos?) then
        -- ignore nested infos of the same tactic, e.g. from expansion
        if (pos', tailPos') != (pos, tailPos) then
          return true
      cs.any (hasNestedTactic pos tailPos)
    | InfoTree.node (Info.ofMacroExpansionInfo _) cs =>
      cs.any (hasNestedTactic pos tailPos)
    | _ => false

end Lean.Elab
