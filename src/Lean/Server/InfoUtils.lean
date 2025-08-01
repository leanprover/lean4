/-
Copyright (c) 2021 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
module

prelude
public import Lean.DocString
public import Lean.PrettyPrinter
public import Lean.Parser.Tactic.Doc
meta import Lean.Parser.Term

public section

namespace Lean.Elab

open Lean.Parser.Tactic.Doc (alternativeOfTactic getTacticExtensionString)

/-- Elaborator information with elaborator context.

It can be thought of as a "thunked" elaboration computation that allows us
to retroactively extract type information, symbol locations, etc.
through arbitrary invocations of `runMetaM` (where the necessary context and state
can be reconstructed from `ctx` and `info.lctx`).

W.r.t. widgets, this is used to tag different parts of expressions in `ppExprTagged`.
This is the input to the RPC call `Lean.Widget.InteractiveDiagnostics.infoToInteractive`.
It carries over information about delaborated
`Info` nodes in a `CodeWithInfos`, and the associated pretty-printing
functionality is purpose-specific to showing the contents of infoview popups.

For use in standard LSP go-to-definition (see `Lean.Server.FileWorker.locationLinksOfInfo`),
all the elaborator information we need for similar tasks is already fully recoverable via
the `InfoTree` structure (see `Lean.Elab.InfoTree.visitM`).
There we use this as a convenience wrapper for queried nodes (e.g. the return value of
`Lean.Elab.InfoTree.hoverableInfoAt?`). It also includes the children info nodes
as additional context (this is unused in the RPC case, as delaboration has no notion of child nodes).

NOTE: This type is for internal use in the infoview/LSP. It should not be used in user widgets.
-/
structure InfoWithCtx where
  ctx  : Elab.ContextInfo
  info : Elab.Info
  children : PersistentArray InfoTree

/--
Visit nodes, passing in a surrounding context (the innermost one combined with all outer ones) and
accumulating results on the way back up. If `preNode` returns `false`, the children of the current
node are skipped and `postNode` is invoked with an empty list of results.
-/
partial def InfoTree.visitM [Monad m]
    (preNode  : ContextInfo → Info → (children : PersistentArray InfoTree) → m Bool := fun _ _ _ => pure true)
    (postNode : ContextInfo → Info → (children : PersistentArray InfoTree) → List (Option α) → m α)
    (ctx? : Option ContextInfo := none) : InfoTree → m (Option α) :=
  go ctx?
where go
  | ctx?, context ctx t => go (ctx.mergeIntoOuter? ctx?) t
  | some ctx, node i cs => do
    let visitChildren ← preNode ctx i cs
    if !visitChildren then
      postNode ctx i cs []
    else
      let as ← cs.toList.mapM (go <| i.updateContext? ctx)
      postNode ctx i cs as
  | none, node .. => panic! "unexpected context-free info tree node"
  | _, hole .. => pure none

/-- `InfoTree.visitM` specialized to `Unit` return type -/
def InfoTree.visitM' [Monad m]
    (preNode  : ContextInfo → Info → (children : PersistentArray InfoTree) → m Bool := fun _ _ _ => pure true)
    (postNode : ContextInfo → Info → (children : PersistentArray InfoTree) → m Unit := fun _ _ _ => pure ())
    (ctx? : Option ContextInfo := none) (t : InfoTree) : m Unit :=
  t.visitM preNode (fun ci i cs _ => postNode ci i cs) ctx? |> discard

/--
  Visit nodes bottom-up, passing in a surrounding context (the innermost one) and the union of nested results (empty at leaves). -/
def InfoTree.collectNodesBottomUpM [Monad m] (p : ContextInfo → Info → PersistentArray InfoTree → List α → m (List α)) (i : InfoTree) : m (List α) :=
  (·.getD []) <$> i.visitM (m := m) (postNode := fun ci i cs as => do p ci i cs (as.filterMap id).flatten)

/--
  Visit nodes bottom-up, passing in a surrounding context (the innermost one) and the union of nested results (empty at leaves). -/
def InfoTree.collectNodesBottomUp (p : ContextInfo → Info → PersistentArray InfoTree → List α → List α) (i : InfoTree) : List α :=
  Id.run <| i.collectNodesBottomUpM (pure <| p · · · ·)

/--
  For every branch of the `InfoTree`, find the deepest node in that branch for which `p` returns
  `some _`  and return the union of all such nodes. The visitor `p` is given a node together with
  its innermost surrounding `ContextInfo`. -/
partial def InfoTree.deepestNodesM [Monad m] (p : ContextInfo → Info → PersistentArray InfoTree → m (Option α)) (infoTree : InfoTree) : m (List α) :=
  infoTree.collectNodesBottomUpM fun ctx i cs rs => do
    if rs.isEmpty then
      match ← p ctx i cs with
      | some r => return [r]
      | none   => return []
    else
      return rs

/--
  For every branch of the `InfoTree`, find the deepest node in that branch for which `p` returns
  `some _`  and return the union of all such nodes. The visitor `p` is given a node together with
  its innermost surrounding `ContextInfo`. -/
partial def InfoTree.deepestNodes (p : ContextInfo → Info → PersistentArray InfoTree → Option α) (infoTree : InfoTree) : List α :=
  Id.run <| infoTree.deepestNodesM (pure <| p · · ·)

partial def InfoTree.foldInfo (f : ContextInfo → Info → α → α) (init : α) : InfoTree → α :=
  go none init
where go ctx? a
  | context ctx t => go (ctx.mergeIntoOuter? ctx?) a t
  | node i ts =>
    let a := match ctx? with
      | none => a
      | some ctx => f ctx i a
    ts.foldl (init := a) (go <| i.updateContext? ctx?)
  | hole _ => a

partial def InfoTree.foldInfoM [Monad m] (f : ContextInfo → Info → α → m α) (init : α) : InfoTree → m α :=
  go none init
where go ctx? a
  | context ctx t => go (ctx.mergeIntoOuter? ctx?) a t
  | node i ts => do
    let a ← match ctx? with
      | none => pure a
      | some ctx => f ctx i a
    ts.foldlM (init := a) (go <| i.updateContext? ctx?)
  | hole _ => pure a

/--
Fold an info tree as follows, while ensuring that the correct `ContextInfo` is supplied at each stage:

 * Nodes are combined with the initial value `init` using `f`, and the result is then combined with the children using a left fold
 * On InfoTree holes, we just return the initial value.

This is like `InfoTree.foldInfo`, but it also passes the whole node to `f` instead of just the head.
-/
partial def InfoTree.foldInfoTree (init : α) (f : ContextInfo → InfoTree → α → α) : InfoTree → α :=
  go none init
where
  /-- `foldInfoTree.go` is like `foldInfoTree` but with an additional outer context parameter `ctx?`. -/
  go ctx? a
  | context ctx t => go (ctx.mergeIntoOuter? ctx?) a t
  | t@(node i ts) =>
    let a := match ctx? with
      | none => a
      | some ctx => f ctx t a
    ts.foldl (init := a) (go <| i.updateContext? ctx?)
  | hole _ => a

def InfoTree.collectTermInfoM [Monad m] (t : InfoTree) (f : ContextInfo → TermInfo → m (Option α)) : m (List α) :=
  t.foldInfoM (init := []) fun ctx info result =>
    match info with
    | Info.ofTermInfo ti => do
      match ← f ctx ti with
      | some a => return a :: result
      | none => return result
    | _ => return result

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
  | ofPartialTermInfo i    => i.stx
  | ofCommandInfo i        => i.stx
  | ofMacroExpansionInfo i => i.stx
  | ofOptionInfo i         => i.stx
  | ofErrorNameInfo i      => i.stx
  | ofFieldInfo i          => i.stx
  | ofCompletionInfo i     => i.stx
  | ofCustomInfo i         => i.stx
  | ofUserWidgetInfo i     => i.stx
  | ofFVarAliasInfo _      => .missing
  | ofFieldRedeclInfo i    => i.stx
  | ofDelabTermInfo i      => i.stx
  | ofChoiceInfo i         => i.stx

def Info.lctx : Info → LocalContext
  | .ofTermInfo i           => i.lctx
  | .ofFieldInfo i          => i.lctx
  | .ofDelabTermInfo i      => i.lctx
  | .ofMacroExpansionInfo i => i.lctx
  | .ofCompletionInfo i     => i.lctx
  | _                       => LocalContext.empty

def Info.pos? (i : Info) : Option String.Pos :=
  i.stx.getPos? (canonicalOnly := true)

def Info.tailPos? (i : Info) : Option String.Pos :=
  i.stx.getTailPos? (canonicalOnly := true)

def Info.range? (i : Info) : Option String.Range :=
  i.stx.getRange? (canonicalOnly := true)

def Info.contains (i : Info) (pos : String.Pos) (includeStop := false) : Bool :=
  i.range?.any (·.contains pos includeStop)

def Info.size? (i : Info) : Option String.Pos := do
  let pos ← i.pos?
  let tailPos ← i.tailPos?
  return tailPos - pos

-- `Info` without position information are considered to have "infinite" size
def Info.isSmaller (i₁ i₂ : Info) : Bool :=
  match i₁.size?, i₂.size? with
  | some sz₁, some sz₂ => sz₁ < sz₂
  | some _, none => true
  | _, _ => false

def Info.occursInside? (i : Info) (hoverPos : String.Pos) : Option String.Pos := do
  let headPos ← i.pos?
  let tailPos ← i.tailPos?
  guard (headPos ≤ hoverPos && hoverPos < tailPos)
  return hoverPos - headPos

def Info.occursInOrOnBoundary (i : Info) (hoverPos : String.Pos) : Bool := Id.run do
  let some headPos := i.pos?
    | return false
  let some tailPos := i.tailPos?
    | return false
  return headPos <= hoverPos && hoverPos <= tailPos

def InfoTree.smallestInfo? (p : Info → Bool) (t : InfoTree) : Option (ContextInfo × Info) :=
  let ts := t.deepestNodes fun ctx i _ => if p i then some (ctx, i) else none

  let infos := ts.filterMap fun (ci, i) => do
    let diff := (← i.tailPos?) - (← i.pos?)
    return (diff, ci, i)

  infos.toArray.getMax? (fun a b => a.1 > b.1) |>.map fun (_, ci, i) => (ci, i)

structure HoverableInfoPrio where
  -- Prefer results directly *after* the hover position (only matters for `includeStop = true`; see #767)
  isHoverPosOnStop : Bool
  -- Relying on the info tree structure is _not_ sufficient for choosing the smallest surrounding node:
  -- `⟨x⟩` expands to an application of a canonical syntax with the span of the anonymous constructor to `x`,
  -- i.e. there are two info tree siblings whose spans are not disjoint and we should choose the smaller node
  -- surrounding the cursor.
  size : Nat
  -- Prefer results for constants over variables (which overlap at declaration names)
  isVariableInfo : Bool
  deriving BEq

instance : Ord HoverableInfoPrio where
  compare i1 i2 := Id.run do
    if i1.isHoverPosOnStop && ! i2.isHoverPosOnStop then
      return .lt
    if ! i1.isHoverPosOnStop && i2.isHoverPosOnStop then
      return .gt
    if i1.size > i2.size then
      return .lt
    if i1.size < i2.size then
      return .gt
    if i1.isVariableInfo && ! i2.isVariableInfo then
      return .lt
    if ! i1.isVariableInfo && i2.isVariableInfo then
      return .gt
    return .eq

instance : LE HoverableInfoPrio := leOfOrd
instance : Max HoverableInfoPrio := maxOfLe

/-- Find an info node, if any, which should be shown on hover/cursor at position `hoverPos`. -/
partial def InfoTree.hoverableInfoAtM? [Monad m] (t : InfoTree) (hoverPos : String.Pos) (includeStop := false)
    (filter : (ctx : ContextInfo) → (info : Info) → (children : PersistentArray InfoTree) →
      (results : List (HoverableInfoPrio × InfoWithCtx)) →
      m (List (HoverableInfoPrio × InfoWithCtx)) := fun _ _ _ results => pure results) :
    m (Option InfoWithCtx) := do
  let postNode ctx info children results : m (Option (HoverableInfoPrio × InfoWithCtx)) := do
    let results ← results.filterMap (fun r? => r?.join) |> filter ctx info children
    let maxPrio? := results.map (·.1) |>.max?
    let bestResult? := results.find? (·.1 == maxPrio?)
    if let some (prio, i) := bestResult? then
      -- Prefer innermost results
      return (prio, i)
    -- We skip `info` nodes associated with the `nullKind` and `withAnnotateState` because they are used by tactics (e.g. `rewrite`) to control
    -- which goal is displayed in the info views. See issue #1403.
    let isAuxInfo := info.stx.isOfKind nullKind
      || info.toElabInfo?.any (·.elaborator == `Lean.Elab.Tactic.evalWithAnnotateState)
    if isAuxInfo then
      return none
    let isEligibleInfoKind := info matches .ofFieldInfo _ | .ofOptionInfo _ | .ofErrorNameInfo _ || info.toElabInfo?.isSome
    let some r := info.stx.getRange? (canonicalOnly := true)
      | return none
    if ! r.contains hoverPos includeStop || ! isEligibleInfoKind then
      return none
    let priority : HoverableInfoPrio := {
      isHoverPosOnStop := r.stop == hoverPos
      size := (r.stop - r.start).byteIdx
      isVariableInfo := info matches .ofTermInfo { expr := .fvar .., .. }
    }
    let result := { ctx, info, children }
    return some (priority, result)
  let results ← t.visitM (m := m) (postNode := postNode)
  let bestResult? : Option InfoWithCtx := results.join.map (·.2)
  if let some bestResult := bestResult? then
    if let .ofTermInfo ti := bestResult.info then
      if ti.expr.isSyntheticSorry then
        return none
  return bestResult?

def Info.type? (i : Info) : MetaM (Option Expr) :=
  match i with
  | Info.ofTermInfo ti      => Meta.inferType ti.expr
  | Info.ofFieldInfo fi     => Meta.inferType fi.val
  | Info.ofDelabTermInfo ti => Meta.inferType ti.expr
  | _ => return none

def Info.docString? (i : Info) : MetaM (Option String) := do
  let env ← getEnv
  match i with
  | .ofDelabTermInfo { docString? := some s, .. } => return s
  | .ofTermInfo ti
  | .ofDelabTermInfo ti =>
    if let some n := ti.expr.constName? then
      return (← findDocString? env n)
  | .ofFieldInfo fi => return ← findDocString? env fi.projName
  | .ofOptionInfo oi =>
    if let some doc ← findDocString? env oi.declName then
      return doc
    if let some decl := (← getOptionDecls).find? oi.optionName then
      return decl.descr
    return none
  | .ofErrorNameInfo eni => do
    let some errorExplanation := getErrorExplanationRaw? (← getEnv) eni.errorName | return none
    return errorExplanation.summaryWithSeverity
  | _ => pure ()
  if let some ei := i.toElabInfo? then
    return ← findDocString? env ei.stx.getKind <||> findDocString? env ei.elaborator
  return none

/-- Construct a hover popup, if any, from an info node in a context.-/
def Info.fmtHover? (ci : ContextInfo) (i : Info) : IO (Option FormatWithInfos) := do
  ci.runMetaM i.lctx do
    let mut fmts := #[]
    let mut infos := ∅
    let modFmt ← try
      let (termFmt, modFmt) ← fmtTermAndModule?
      if let some f := termFmt then
        fmts := fmts.push f.fmt
        infos := f.infos
      pure modFmt
    catch _ => pure none
    if let some m ← i.docString? then
      fmts := fmts.push m
    if let some f := modFmt then
      fmts := fmts.push f
    if fmts.isEmpty then
      return none
    else
      return some ⟨f!"\n***\n".joinSep fmts.toList, infos⟩

where
  fmtModule? (decl : Name) : MetaM (Option Format) := do
    let some mod ← findModuleOf? decl | return none
    return some f!"*import {mod}*"

  fmtTermAndModule? : MetaM (Option FormatWithInfos × Option Format) := do
    match i with
    | Info.ofTermInfo ti =>
      let e ← instantiateMVars ti.expr
      if e.isSort then
        -- Types of sorts are funny to look at in widgets, but ultimately not very helpful
        return (none, none)
      let tp ← instantiateMVars (← Meta.inferType e)
      let tpFmt ← Meta.ppExpr tp
      if let .const c _ := e then
        let eFmt ← PrettyPrinter.ppSignature c
        return (some { eFmt with fmt := f!"```lean\n{eFmt.fmt}\n```" }, ← fmtModule? c)
      let eFmt ← Meta.ppExpr e
      -- Try not to show too scary internals
      let showTerm := if let .fvar _ := e then
        if let some ldecl := (← getLCtx).findFVar? e then
          !ldecl.userName.hasMacroScopes
        else false
      else isAtomicFormat eFmt
      let fmt := if showTerm then f!"{eFmt} : {tpFmt}" else tpFmt
      return (some f!"```lean\n{fmt}\n```", none)
    | Info.ofFieldInfo fi =>
      let tp ← Meta.inferType fi.val
      let tpFmt ← Meta.ppExpr tp
      return (some f!"```lean\n{fi.fieldName} : {tpFmt}\n```", none)
    | _ => return (none, none)

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
    let Info.ofTacticInfo ti := i
      | return gs
    let (some pos, some tailPos) := (i.pos?, i.tailPos?)
      | return gs
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
          -- consider every position unindented after an empty `by` to support "hanging" `by` uses
          indented := (text.toPosition pos).column > (text.toPosition hoverPos).column && !isEmptyBy ti.stx
          -- use goals just before cursor as fall-back only
          -- thus for `(by foo)`, placing the cursor after `foo` shows its state as long
          -- as there is no state on `)`
          priority := if hoverPos.byteIdx == tailPos.byteIdx + trailSize then 0 else 1
        }]
    return gs
  let maxPrio? := gs.map (·.priority) |>.max?
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
  isEmptyBy (stx : Syntax) : Bool :=
    -- there are multiple `by` kinds with the same structure
    stx.getNumArgs == 2 && stx[0].isToken "by" && stx[1].getNumArgs == 1 && stx[1][0].isMissing


partial def InfoTree.termGoalAt? (t : InfoTree) (hoverPos : String.Pos) : Option InfoWithCtx :=
  -- In the case `f a b`, where `f` is an identifier, the term goal at `f` should be the goal for the full application `f a b`.
  let filter ctx info children results :=
    if info.stx.isOfKind ``Parser.Term.app && info.stx[0].isIdent then
      results.filter (·.2.info.stx != info.stx[0])
    else
      results
  hoverableInfoAtM? (m := Id) t hoverPos (includeStop := true) (filter := filter)

end Lean.Elab
