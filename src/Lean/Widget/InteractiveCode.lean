/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
module

prelude
public import Lean.Server.Rpc.Basic
public import Lean.Server.InfoUtils
public import Lean.Widget.TaggedText
public import Lean.Widget.Basic

public section

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
    match pm.get? info.subexprPos with
    | some a => merger info a
    | none => pure info
  )

def CodeWithInfos.pretty (tt : CodeWithInfos) :=
  tt.stripTags

def SubexprInfo.withDiffTag (tag : DiffTag) (c : SubexprInfo) : SubexprInfo :=
  { c with diffStatus? := some tag }

/-- Tags pretty-printed code with infos from the delaborator. -/
partial def tagCodeInfos (ctx : Elab.ContextInfo) (infos : SubExpr.PosMap Elab.Info) (tt : TaggedText (Nat × Nat))
    : BaseIO CodeWithInfos :=
  go tt
where
  go (tt : TaggedText (Nat × Nat)) : BaseIO (TaggedText SubexprInfo) :=
    tt.rewriteM fun (n, _) subTt => do
      match infos.get? n with
      | none   => go subTt
      | some i =>
        let t : SubexprInfo := {
          info := ← WithRpcRef.mk { ctx, info := i, children := .empty }
          subexprPos := n
        }
        return TaggedText.tag t (← go subTt)

open PrettyPrinter Delaborator in
/--
Pretty prints the expression `e` using delaborator `delab`, returning an object that represents
the pretty printed syntax paired with information needed to support hovers.
-/
def ppExprTagged (e : Expr) (delab : Delab := Delaborator.delab) : MetaM CodeWithInfos := do
  if pp.raw.get (← getOptions) then
    let e ← if getPPInstantiateMVars (← getOptions) then instantiateMVars e else pure e
    return .text (toString e)
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
  tagCodeInfos ctx infos tt

end Lean.Widget
