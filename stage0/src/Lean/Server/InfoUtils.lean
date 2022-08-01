/-
Copyright (c) 2021 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.DocString
import Lean.Elab.InfoTree
import Lean.PrettyPrinter
import Lean.Util.Sorry

protected structure String.Range where
  start : String.Pos
  stop  : String.Pos
  deriving Inhabited, Repr, BEq, Hashable

def String.Range.contains (r : String.Range) (pos : String.Pos) (includeStop := false) : Bool :=
  r.start <= pos && (if includeStop then pos <= r.stop else pos < r.stop)

def Lean.Syntax.getRange? (stx : Syntax) (originalOnly := false) : Option String.Range :=
  match stx.getPos? originalOnly, stx.getTailPos? originalOnly with
  | some start, some stop => some { start, stop }
  | _,          _         => none

namespace Lean.Elab

/-- Visit nodes, passing in a surrounding context (the innermost one) and accumulating results on the way back up. -/
partial def InfoTree.visitM [Monad m] [Inhabited α]
    (preNode  : ContextInfo → Info → (children : Std.PersistentArray InfoTree) → m Unit := fun _ _ _ => pure ())
    (postNode : ContextInfo → Info → (children : Std.PersistentArray InfoTree) → List (Option α) → m α)
    : InfoTree → m (Option α) :=
  go none
where go
  | _, context ctx t => go ctx t
  | some ctx, node i cs => do
    preNode ctx i cs
    let as ← cs.toList.mapM (go <| i.updateContext? ctx)
    postNode ctx i cs as
  | none, node .. => panic! "unexpected context-free info tree node"
  | _, hole .. => pure none

/--
  Visit nodes bottom-up, passing in a surrounding context (the innermost one) and the union of nested results (empty at leaves). -/
def InfoTree.collectNodesBottomUp (p : ContextInfo → Info → Std.PersistentArray InfoTree → List α → List α) (i : InfoTree) : List α :=
  i.visitM (m := Id) (postNode := fun ci i cs as => p ci i cs (as.filterMap id).join) |>.getD []

/--
  For every branch of the `InfoTree`, find the deepest node in that branch for which `p` returns
  `some _`  and return the union of all such nodes. The visitor `p` is given a node together with
  its innermost surrounding `ContextInfo`. -/
partial def InfoTree.deepestNodes (p : ContextInfo → Info → Std.PersistentArray InfoTree → Option α) (infoTree : InfoTree) : List α :=
  infoTree.collectNodesBottomUp fun ctx i cs rs =>
    if rs.isEmpty then
      match p ctx i cs with
      | some r => [r]
      | none   => []
    else
      rs

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
  | ofMacroExpansionInfo i => i.stx
  | ofFieldInfo i          => i.stx
  | ofCompletionInfo i     => i.stx
  | ofCustomInfo i         => i.stx
  | ofUserWidgetInfo i     => i.stx

def Info.lctx : Info → LocalContext
  | Info.ofTermInfo i  => i.lctx
  | Info.ofFieldInfo i => i.lctx
  | _                  => LocalContext.empty

def Info.pos? (i : Info) : Option String.Pos :=
  i.stx.getPos? (originalOnly := true)

def Info.tailPos? (i : Info) : Option String.Pos :=
  i.stx.getTailPos? (originalOnly := true)

def Info.range? (i : Info) : Option String.Range :=
  i.stx.getRange? (originalOnly := true)

def Info.contains (i : Info) (pos : String.Pos) (includeStop := false) : Bool :=
  i.range?.any (·.contains pos includeStop)

def Info.size? (i : Info) : Option String.Pos := do
  let pos ← i.pos?
  let tailPos ← i.tailPos?
  return tailPos - pos

-- `Info` without position information are considered to have "infinite" size
def Info.isSmaller (i₁ i₂ : Info) : Bool :=
  match i₁.size?, i₂.pos? with
  | some sz₁, some sz₂ => sz₁ < sz₂
  | some _, none => true
  | _, _ => false

def Info.occursBefore? (i : Info) (hoverPos : String.Pos) : Option String.Pos := do
  let tailPos ← i.tailPos?
  guard (tailPos ≤ hoverPos)
  return hoverPos - tailPos

def Info.occursInside? (i : Info) (hoverPos : String.Pos) : Option String.Pos := do
  let headPos ← i.pos?
  let tailPos ← i.tailPos?
  guard (headPos ≤ hoverPos && hoverPos < tailPos)
  return hoverPos - headPos

def InfoTree.smallestInfo? (p : Info → Bool) (t : InfoTree) : Option (ContextInfo × Info) :=
  let ts := t.deepestNodes fun ctx i _ => if p i then some (ctx, i) else none

  let infos := ts.map fun (ci, i) =>
    let diff := i.tailPos?.get! - i.pos?.get!
    (diff, ci, i)

  infos.toArray.getMax? (fun a b => a.1 > b.1) |>.map fun (_, ci, i) => (ci, i)

/-- Find an info node, if any, which should be shown on hover/cursor at position `hoverPos`. -/
partial def InfoTree.hoverableInfoAt? (t : InfoTree) (hoverPos : String.Pos) (includeStop := false) (omitAppFns := false) : Option (ContextInfo × Info) := Id.run do
  let results := t.visitM (m := Id) (postNode := fun ctx i _ results => do
    let mut results := results.bind (·.getD [])
    if omitAppFns && i.stx.isOfKind ``Parser.Term.app && i.stx[0].isIdent then
      results := results.filter (·.2.2.stx != i.stx[0])
    if results.isEmpty && (i matches Info.ofFieldInfo _ || i.toElabInfo?.isSome) && i.contains hoverPos includeStop then
      let r := i.range?.get!
      let priority :=
        if r.stop == hoverPos then
          0  -- prefer results directly *after* the hover position (only matters for `includeStop = true`; see #767)
        else if i matches .ofTermInfo { expr := .fvar .., .. } then
          0  -- prefer results for constants over variables (which overlap at declaration names)
        else 1
      [(priority, ctx, i)]
    else
      results) |>.getD []
  let maxPrio? := results.map (·.1) |>.maximum?
  let res? := results.find? (·.1 == maxPrio?) |>.map (·.2)
  if let some (_, i) := res? then
    if let .ofTermInfo ti := i then
      if ti.expr.isSyntheticSorry then
        return none
  return res?

def Info.type? (i : Info) : MetaM (Option Expr) :=
  match i with
  | Info.ofTermInfo ti => Meta.inferType ti.expr
  | Info.ofFieldInfo fi => Meta.inferType fi.val
  | _ => return none

def Info.docString? (i : Info) : MetaM (Option String) := do
  let env ← getEnv
  if let Info.ofTermInfo ti := i then
    if let some n := ti.expr.constName? then
      return ← findDocString? env n
  if let Info.ofFieldInfo fi := i then
    return ← findDocString? env fi.projName
  if let some ei := i.toElabInfo? then
    return ← findDocString? env ei.elaborator <||> findDocString? env ei.stx.getKind
  return none

/-- Construct a hover popup, if any, from an info node in a context.-/
def Info.fmtHover? (ci : ContextInfo) (i : Info) : IO (Option Format) := do
  ci.runMetaM i.lctx do
    let mut fmts := #[]
    try
      if let some f ← fmtTerm? then
        fmts := fmts.push f
    catch _ => pure ()
    if let some m ← i.docString? then
      fmts := fmts.push m
    if fmts.isEmpty then
      return none
    else
      return f!"\n***\n".joinSep fmts.toList

where
  fmtTerm? : MetaM (Option Format) := do
    match i with
    | Info.ofTermInfo ti =>
      let e ← instantiateMVars ti.expr
      if e.isSort then
        -- Types of sorts are funny to look at in widgets, but ultimately not very helpful
        return none
      let tp ← instantiateMVars (← Meta.inferType e)
      let tpFmt ← Meta.ppExpr tp
      if e.isConst then
        -- Recall that `ppExpr` adds a `@` if the constant has implicit arguments, and it is quite distracting
        let eFmt ← withOptions (pp.fullNames.set · true |> (pp.universes.set · true)) <| PrettyPrinter.ppConst e
        return some f!"```lean
{eFmt} : {tpFmt}
```"
      else
        let eFmt ← Meta.ppExpr e
        -- Try not to show too scary internals
        let fmt := if isAtomicFormat eFmt then f!"{eFmt} : {tpFmt}" else f!"{tpFmt}"
        return some f!"```lean
{fmt}
```"
    | Info.ofFieldInfo fi =>
      let tp ← Meta.inferType fi.val
      let tpFmt ← Meta.ppExpr tp
      return some f!"```lean
{fi.fieldName} : {tpFmt}
```"
    | _ => return none

  isAtomicFormat : Format → Bool
    | Std.Format.text _    => true
    | Std.Format.group f _ => isAtomicFormat f
    | Std.Format.nest _ f  => isAtomicFormat f
    | Std.Format.tag _ f   => isAtomicFormat f
    | _                    => false

structure GoalsAtResult where
  ctxInfo    : ContextInfo
  tacticInfo : TacticInfo
  useAfter   : Bool
  /-- Whether the tactic info is further indented than the hover position. -/
  indented   : Bool
  -- for overlapping goals, only keep those of the highest reported priority
  priority   : Nat

/--
  Try to retrieve `TacticInfo` for `hoverPos`.
  We retrieve all `TacticInfo` nodes s.t. `hoverPos` is inside the node's range plus trailing whitespace.
  We usually prefer the innermost such nodes so that for composite tactics such as `induction`, we show the nested proofs' states.
  However, if `hoverPos` is after the tactic, we prefer nodes that are not indented relative to it, meaning that e.g. at `|` in
  ```lean
  have := by
    exact foo
  |
  ```
  we show the (final, see below) state of `have`, not `exact`.

  Moreover, we instruct the LSP server to use the state after tactic execution if
  - the hover position is after the info's start position *and*
  - there is no nested tactic info after the hover position (tactic combinators should decide for themselves
    where to show intermediate states by calling `withTacticInfoContext`) -/
partial def InfoTree.goalsAt? (text : FileMap) (t : InfoTree) (hoverPos : String.Pos) : List GoalsAtResult :=
  let gs := t.collectNodesBottomUp fun ctx i cs gs => Id.run do
    if let Info.ofTacticInfo ti := i then
      if let (some pos, some tailPos) := (i.pos?, i.tailPos?) then
        let trailSize := i.stx.getTrailingSize
        -- show info at EOF even if strictly outside token + trail
        let atEOF := tailPos.byteIdx + trailSize == text.source.endPos.byteIdx
        -- include at least one trailing character (see also `priority` below)
        if pos ≤ hoverPos ∧ (hoverPos.byteIdx < tailPos.byteIdx + max 1 trailSize || atEOF) then
          -- overwrite bottom-up results according to "innermost" heuristics documented above
          if gs.isEmpty || hoverPos ≥ tailPos && gs.all (·.indented) then
            return [{
              ctxInfo := ctx
              tacticInfo := ti
              useAfter := hoverPos > pos && !cs.any (hasNestedTactic pos tailPos)
              indented := (text.toPosition pos).column > (text.toPosition hoverPos).column
              -- use goals just before cursor as fall-back only
              -- thus for `(by foo)`, placing the cursor after `foo` shows its state as long
              -- as there is no state on `)`
              priority := if hoverPos.byteIdx == tailPos.byteIdx + trailSize then 0 else 1
            }]
    return gs
  let maxPrio? := gs.map (·.priority) |>.maximum?
  gs.filter (some ·.priority == maxPrio?)
where
  hasNestedTactic (pos tailPos) : InfoTree → Bool
    | InfoTree.node i@(Info.ofTacticInfo _) cs => Id.run do
      if let `(by $_) := i.stx then
        return false  -- ignore term-nested proofs such as in `simp [show p by ...]`
      if let (some pos', some tailPos') := (i.pos?, i.tailPos?) then
        -- ignore preceding nested infos
        -- ignore nested infos of the same tactic, e.g. from expansion
        if tailPos' > hoverPos && (pos', tailPos') != (pos, tailPos) then
          return true
      cs.any (hasNestedTactic pos tailPos)
    | InfoTree.node (Info.ofMacroExpansionInfo _) cs =>
      cs.any (hasNestedTactic pos tailPos)
    | _ => false

partial def InfoTree.termGoalAt? (t : InfoTree) (hoverPos : String.Pos) : Option (ContextInfo × Info) :=
  -- In the case `f a b`, where `f` is an identifier, the term goal at `f` should be the goal for the full application `f a b`.
  hoverableInfoAt? t hoverPos (includeStop := true) (omitAppFns := true)

partial def InfoTree.hasSorry : InfoTree → IO Bool :=
  go none
where go ci?
  | .context ci t => go ci t
  | .node i cs =>
    if let (some ci, .ofTermInfo ti) := (ci?, i) then do
      let expr ← ti.runMetaM ci (instantiateMVars ti.expr)
      return expr.hasSorry
      -- we assume that `cs` are subterms of `ti.expr` and
      -- thus do not have to be checked as well
    else
      cs.anyM (go ci?)
  | _ => return false

end Lean.Elab
