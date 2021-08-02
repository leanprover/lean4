/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.PrettyPrinter
import Lean.Server.Rpc.Basic
import Lean.Server.Rpc.RequestHandling
import Lean.Widget.TaggedText

/-! RPC infrastructure for storing/formatting `Expr`s with environment and subexpression information. -/

namespace Lean.Widget
open Server

/-- Bundles an `Expr` with its `MetaM` context. -/
structure ExprWithCtx where
  expr          : Expr
  env           : Environment
  mctx          : MetavarContext
  lctx          : LocalContext
  options       : Options
  currNamespace : Name
  openDecls     : List OpenDecl
  deriving Inhabited, RpcEncoding with { withRef := true }

/-- We traverse expressions lazily when the client requests it. -/
abbrev LazyExprWithCtx := Unit → IO ExprWithCtx
deriving instance RpcEncoding with { withRef := true } for LazyExprWithCtx

builtin_initialize
  registerRpcCallHandler `Lean.Widget.LazyExprWithCtx.get (WithRpcRef LazyExprWithCtx) (WithRpcRef ExprWithCtx) fun ⟨e⟩ => RequestM.asTask do WithRpcRef.mk <$> e ()

/-- Pretty-printed expressions are tagged with their (lazily-accessible) source `Expr`s. -/
-- TODO(WN): use the `InfoTree` map when the delaborator supports it
abbrev ExprText := TaggedText (WithRpcRef LazyExprWithCtx)

namespace ExprWithCtx

def runMetaM (e : ExprWithCtx) (x : MetaM α) : IO α := do
  let ((ret, _), _) ← x
    |>.run { lctx := e.lctx } { mctx := e.mctx }
    |>.toIO { options := e.options, currNamespace := e.currNamespace, openDecls := e.openDecls }
            { env := e.env }
  return ret

open Expr in
/-- Find a subexpression of `e` using the pretty-printer address scheme. -/
partial def traverse (e : ExprWithCtx) (addr : Nat) : MetaM ExprWithCtx := do
  let e := { e with expr := ← Meta.instantiateMVars e.expr }
  let e ← go (tritsLE [] addr |>.drop 1) e
  return e
where
  tritsLE (acc : List Nat) (n : Nat) : List Nat :=
    if n == 0 then acc
    else tritsLE (n % 3 :: acc) (n / 3)

  go (addr : List Nat) (e : ExprWithCtx) : MetaM ExprWithCtx := do
    match addr with
    | [] => e
    | a::as => do
      let go' (e' : Expr) := do
        go as { e with expr := e', lctx := ← getLCtx }

      let eExpr ← match a, e.expr with
        | 0, app e₁ e₂ _       => go' e₁
        | 1, app e₁ e₂ _       => go' e₂
        | 0, lam _ e₁ e₂ _     => go' e₁
        | 1, lam n e₁ e₂ data     =>
          Meta.withLocalDecl n data.binderInfo e₁ fun fvar =>
            go' (e₂.instantiate1 fvar)
        | 0, forallE _ e₁ e₂ _ => go' e₁
        | 1, forallE n e₁ e₂ data =>
          Meta.withLocalDecl n data.binderInfo e₁ fun fvar =>
            go' (e₂.instantiate1 fvar)
        | 0, letE _ e₁ e₂ e₃ _ => go' e₁
        | 1, letE _ e₁ e₂ e₃ _ => go' e₂
        | 2, letE n e₁ e₂ e₃ _ =>
          Meta.withLetDecl n e₁ e₂ fun fvar => do
            go' (e₃.instantiate1 fvar)
        | 0, mdata _ e₁ _      => go' e₁
        | 0, proj _ _ e₁ _     => go' e₁
        | _, _ => e -- panic! s!"cannot descend {a} into {e.expr}"

/-- Pretty-print the expression and its subexpression information. -/
def fmt (e : ExprWithCtx) : MetaM ExprText := do
  let opts ← getOptions
  let lctx := (← getLCtx).sanitizeNames.run' { options := opts }
  Meta.withLCtx lctx #[] do
    let fmt ← Meta.ppExpr e.expr
    let tt := TaggedText.prettyTagged fmt
    tt.map fun n =>
      WithRpcRef.mk fun () => e.runMetaM (e.traverse n)

/-- Like `fmt` but with `pp.all` set at the top-level expression. -/
def fmtExplicit (e : ExprWithCtx) : MetaM ExprText := do
  let opts ← getOptions
  let lctx := (← getLCtx).sanitizeNames.run' { options := opts }
  Meta.withLCtx lctx #[] do
    let currNs ← getCurrNamespace
    let openDecls ← getOpenDecls
    let optsPerPos := Std.RBMap.ofList [(1, KVMap.empty.setBool `pp.all true)]
    let stx ← PrettyPrinter.delab currNs openDecls e.expr optsPerPos
    let stx := (sanitizeSyntax stx).run' { options := opts }
    let stx ← PrettyPrinter.parenthesizeTerm stx
    let fmt ← PrettyPrinter.formatTerm stx
    let tt := TaggedText.prettyTagged fmt
    tt.map fun n =>
      WithRpcRef.mk fun () => e.runMetaM (e.traverse n)

def inferType (e : ExprWithCtx) : MetaM ExprWithCtx := do
  return { e with expr := ← Meta.inferType e.expr }

initialize
  registerRpcCallHandler `Lean.Widget.ExprWithCtx.fmt         (WithRpcRef ExprWithCtx) ExprText                 fun ⟨e⟩ => RequestM.asTask do e.runMetaM (fmt e)
  registerRpcCallHandler `Lean.Widget.ExprWithCtx.fmtExplicit (WithRpcRef ExprWithCtx) ExprText                 fun ⟨e⟩ => RequestM.asTask do e.runMetaM (fmtExplicit e)
  registerRpcCallHandler `Lean.Widget.ExprWithCtx.inferType   (WithRpcRef ExprWithCtx) (WithRpcRef ExprWithCtx) fun ⟨e⟩ => RequestM.asTask do WithRpcRef.mk <$> e.runMetaM (inferType e)

end ExprWithCtx
end Lean.Widget
