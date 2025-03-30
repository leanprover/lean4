/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
prelude
import Lean.Server.Rpc.Basic
import Lean.Server.InfoUtils
import Lean.Widget.TaggedText
import Lean.Widget.Basic

/-! RPC infrastructure for storing and formatting code fragments, in particular `Expr`s,
with environment and subexpression information. -/

namespace Lean.Widget
open Server

/-- A tag indicating the diff status of the expression. Used when showing tactic diffs. -/
inductive DiffTag where
  | wasChanged
  | willChange
  | wasDeleted
  | willDelete
  | wasInserted
  | willInsert
  deriving ToJson, FromJson

/-- Information about a subexpression within delaborated code. -/
structure SubexprInfo where
  /-- The `Elab.Info` node with the semantics of this part of the output. -/
  info : WithRpcRef Lean.Elab.InfoWithCtx
  /-- The position of this subexpression within the top-level expression. See `Lean.SubExpr`. -/
  subexprPos : Lean.SubExpr.Pos
  -- TODO(WN): add fields for semantic highlighting
  -- kind : Lsp.SymbolKind
  /-- In certain situations such as when goal states change between positions in a tactic-mode proof,
  we can show subexpression-level diffs between two expressions. This field asks the renderer to
  display the subexpression as in a diff view (e.g. red/green like `git diff`). -/
  diffStatus? : Option DiffTag := none
  deriving RpcEncodable

/-- Pretty-printed syntax (usually but not necessarily an `Expr`) with embedded `Info`s. -/
abbrev CodeWithInfos := TaggedText SubexprInfo

def CodeWithInfos.mergePosMap [Monad m] (merger : SubexprInfo → α → m SubexprInfo) (pm : Lean.SubExpr.PosMap α) (tt : CodeWithInfos) : m CodeWithInfos :=
  if pm.isEmpty then return tt else
  tt.mapM (fun (info : SubexprInfo) =>
    match pm.find? info.subexprPos with
    | some a => merger info a
    | none => pure info
  )

def CodeWithInfos.pretty (tt : CodeWithInfos) :=
  tt.stripTags

def SubexprInfo.withDiffTag (tag : DiffTag) (c : SubexprInfo) : SubexprInfo :=
  { c with diffStatus? := some tag }

/-- Tags pretty-printed code with infos from the delaborator. -/
partial def tagCodeInfos (ctx : Elab.ContextInfo) (infos : SubExpr.PosMap Elab.Info) (tt : TaggedText (Nat × Nat))
    : CodeWithInfos :=
  go tt
where
  go (tt : TaggedText (Nat × Nat)) :=
    tt.rewrite fun (n, _) subTt =>
      match infos.find? n with
      | none   => go subTt
      | some i =>
        let t : SubexprInfo := {
          info := WithRpcRef.mk { ctx, info := i, children := .empty }
          subexprPos := n
        }
        TaggedText.tag t (go subTt)

def ppExprTagged (e : Expr) (explicit : Bool := false) : MetaM CodeWithInfos := do
  if pp.raw.get (← getOptions) then
    return .text (toString (← instantiateMVars e))
  let delab := open PrettyPrinter.Delaborator in
    if explicit then
      withOptionAtCurrPos pp.tagAppFns.name true do
      withOptionAtCurrPos pp.explicit.name true do
      withOptionAtCurrPos pp.mvars.anonymous.name true do
        delabApp
    else
      withOptionAtCurrPos pp.proofs.name true do
      withOptionAtCurrPos pp.sorrySource.name true do
        delab
  let mut e := e
  -- When hovering over a metavariable, we want to see its value, even if `pp.instantiateMVars` is false.
  if explicit && e.isMVar then
    if let some e' ← getExprMVarAssignment? e.mvarId! then
      e := e'
  let ⟨fmt, infos⟩ ← PrettyPrinter.ppExprWithInfos e (delab := delab)
  let tt := TaggedText.prettyTagged fmt
  let ctx := {
    env           := (← getEnv)
    mctx          := (← getMCtx)
    options       := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls     := (← getOpenDecls)
    fileMap       := default
    ngen          := (← getNGen)
  }
  return tagCodeInfos ctx infos tt

end Lean.Widget
