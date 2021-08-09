/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.PrettyPrinter
import Lean.Server.Rpc.Basic
import Lean.Server.Rpc.RequestHandling
import Lean.Widget.TaggedText
import Lean.Widget.Data

/-! RPC infrastructure for storing/formatting `Expr`s with environment and subexpression information. -/

namespace Lean.Widget
open Server

structure ExprWithCtx where
  ctx : Elab.ContextInfo
  lctx : LocalContext
  expr : Expr
  deriving Inhabited, RpcEncoding with { withRef := true }

namespace ExprWithCtx

open Expr in
/-- Find a subexpression of `e` using the pretty-printer address scheme. -/
-- NOTE(WN): not currently in use
partial def traverse (e : Expr) (addr : Nat) : MetaM (LocalContext × Expr):= do
  let e ← Meta.instantiateMVars e
  go (tritsLE [] addr |>.drop 1) (← getLCtx) e
where
  tritsLE (acc : List Nat) (n : Nat) : List Nat :=
    if n == 0 then acc
    else tritsLE (n % 3 :: acc) (n / 3)

  go (addr : List Nat) (lctx : LocalContext) (e : Expr) : MetaM (LocalContext × Expr) := do
    match addr with
    | [] => (lctx, e)
    | a::as => do
      let go' (e' : Expr) := do
        go as (← getLCtx) e'

      let eExpr ← match a, e with
        | 0, app e₁ e₂ _      => go' e₁
        | 1, app e₁ e₂ _      => go' e₂
        | 0, lam _ e₁ e₂ _    => go' e₁
        | 1, lam n e₁ e₂ data =>
          Meta.withLocalDecl n data.binderInfo e₁ fun fvar =>
            go' (e₂.instantiate1 fvar)
        | 0, forallE _ e₁ e₂ _    => go' e₁
        | 1, forallE n e₁ e₂ data =>
          Meta.withLocalDecl n data.binderInfo e₁ fun fvar =>
            go' (e₂.instantiate1 fvar)
        | 0, letE _ e₁ e₂ e₃ _ => go' e₁
        | 1, letE _ e₁ e₂ e₃ _ => go' e₂
        | 2, letE n e₁ e₂ e₃ _ =>
          Meta.withLetDecl n e₁ e₂ fun fvar => do
            go' (e₃.instantiate1 fvar)
        | 0, mdata _ e₁ _  => go' e₁
        | 0, proj _ _ e₁ _ => go' e₁
        | _, _             => (lctx, e) -- panic! s!"cannot descend {a} into {e.expr}"

-- TODO(WN): should these go in `Lean.PrettyPrinter` ?
open PrettyPrinter in
private def formatWithOpts (e : Expr) (optsPerPos : Delaborator.OptionsPerPos)
    : MetaM (Format × Std.RBMap Nat Elab.Info compare) := do
    let currNamespace ← getCurrNamespace
    let openDecls ← getOpenDecls
    let opts ← getOptions
    let (stx, infos) ← PrettyPrinter.delabCore currNamespace openDecls e
    let stx := sanitizeSyntax stx |>.run' { options := opts }
    let stx ← PrettyPrinter.parenthesizeTerm stx
    let fmt ← PrettyPrinter.formatTerm stx
    return (fmt, infos)

/-- Pretty-print the expression and its subexpression information. -/
def formatInfos (e : Expr) : MetaM (Format × Std.RBMap Nat Elab.Info compare) :=
  formatWithOpts e {}

/-- Like `formatM` but with `pp.all` set at the top-level expression. -/
def formatExplicitInfos (e : Expr) : MetaM (Format × Std.RBMap Nat Elab.Info compare) := do
  let optsPerPos := Std.RBMap.ofList [(1, KVMap.empty.setBool `pp.all true)]
  formatWithOpts e optsPerPos

/-- Tags a pretty-printed `Expr` with infos from the delaborator. -/
partial def tagExprInfos (ctx : Elab.ContextInfo) (lctx : LocalContext) (infos : Std.RBMap Nat Elab.Info compare) (tt : TaggedText Nat)
    : CodeWithInfos :=
  go tt
where
  go (tt : TaggedText Nat) :=
    tt.rewrite fun n subTt =>
      match infos.find? n with
      | none   => go subTt
      | some i => TaggedText.tag (WithRpcRef.mk { ctx, lctx, info := i }) (go subTt)

def inferType (e : Expr) : MetaM ExprWithCtx := do
  let ctx := {
    env := ← getEnv
    mctx := ← getMCtx
    options := ← getOptions
    currNamespace := ← getCurrNamespace
    openDecls := ← getOpenDecls
    fileMap := arbitrary }
  return { ctx, lctx := ← getLCtx, expr := e}

def tagged (e : Expr) : MetaM CodeWithInfos := do
  let (fmt, infos) ← formatInfos e
  let tt := TaggedText.prettyTagged fmt
  let ctx := {
    env := ← getEnv
    mctx := ← getMCtx
    options := ← getOptions
    currNamespace := ← getCurrNamespace
    openDecls := ← getOpenDecls
    fileMap := arbitrary }
  tagExprInfos ctx (← getLCtx) infos tt

def taggedExplicit (e : Expr) : MetaM CodeWithInfos := do
  let (fmt, infos) ← formatExplicitInfos e
  let tt := TaggedText.prettyTagged fmt
  let ctx := {
    env := ← getEnv
    mctx := ← getMCtx
    options := ← getOptions
    currNamespace := ← getCurrNamespace
    openDecls := ← getOpenDecls
    fileMap := arbitrary }
  tagExprInfos ctx (← getLCtx) infos tt

builtin_initialize
  registerRpcCallHandler `Lean.Widget.ExprWithCtx.tagged         (WithRpcRef ExprWithCtx) CodeWithInfos            fun ⟨e⟩ => RequestM.asTask do e.ctx.runMetaM e.lctx (tagged e.expr)
  registerRpcCallHandler `Lean.Widget.ExprWithCtx.taggedExplicit (WithRpcRef ExprWithCtx) CodeWithInfos            fun ⟨e⟩ => RequestM.asTask do e.ctx.runMetaM e.lctx (taggedExplicit e.expr)
  registerRpcCallHandler `Lean.Widget.ExprWithCtx.inferType      (WithRpcRef ExprWithCtx) (WithRpcRef ExprWithCtx) fun ⟨e⟩ => RequestM.asTask do WithRpcRef.mk <$> e.ctx.runMetaM e.lctx (inferType e.expr)

end ExprWithCtx
end Lean.Widget
