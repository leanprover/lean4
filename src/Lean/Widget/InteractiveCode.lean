/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.PrettyPrinter
import Lean.Server.Rpc.Basic
import Lean.Widget.TaggedText
import Lean.Widget.Basic

/-! RPC infrastructure for storing and formatting code fragments, in particular `Expr`s,
with environment and subexpression information. -/

namespace Lean.Widget
open Server

/-- Information about a subexpression within delaborated code. -/
structure SubexprInfo where
  /-- The `Elab.Info` node with the semantics of this part of the output. -/
  info : WithRpcRef InfoWithCtx
  /-- The position of this subexpression within the top-level expression.
  See `Lean.SubExpr`. -/
  subexprPos : Lean.SubExpr.Pos
  -- TODO(WN): add fields for semantic highlighting
  -- kind : Lsp.SymbolKind
  deriving Inhabited, RpcEncodable

/-- Pretty-printed syntax (usually but not necessarily an `Expr`) with embedded `Info`s. -/
abbrev CodeWithInfos := TaggedText SubexprInfo

def CodeWithInfos.pretty (tt : CodeWithInfos) :=
  tt.stripTags

/-- Tags a pretty-printed `Expr` with infos from the delaborator. -/
partial def tagExprInfos (ctx : Elab.ContextInfo) (infos : Std.RBMap Nat Elab.Info compare) (tt : TaggedText (Nat × Nat))
    : CodeWithInfos :=
  go tt
where
  go (tt : TaggedText (Nat × Nat)) :=
    tt.rewrite fun (n, _) subTt =>
      match infos.find? n with
      | none   => go subTt
      | some i => TaggedText.tag ⟨WithRpcRef.mk { ctx, info := i }, n⟩ (go subTt)

def ppExprTagged (e : Expr) (explicit : Bool := false) : MetaM CodeWithInfos := do
  let delab := open PrettyPrinter.Delaborator in
    if explicit then
      withOptionAtCurrPos pp.tagAppFns.name true do
      withOptionAtCurrPos pp.explicit.name true do
        delabAppImplicit <|> delabAppExplicit
    else
      delab
  let (fmt, infos) ← PrettyPrinter.ppExprWithInfos e (delab := delab)
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
  return tagExprInfos ctx infos tt

end Lean.Widget
