/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Marc Huisinga
-/
prelude
import Lean.Server.Completion.CompletionItemData
import Lean.Server.Completion.CompletionInfoSelection

namespace Lean.Lsp

/--
Identifier that is sent from the server to the client as part of the `CompletionItem.data?` field.
Needed to resolve the `CompletionItem` when the client sends a `completionItem/resolve` request
for that item, again containing the `data?` field provided by the server.
-/
inductive CompletionIdentifier where
  | const (declName : Name)
  | fvar  (id       : FVarId)
  deriving FromJson, ToJson

/--
`CompletionItemData` that contains additional information to identify the item
in order to resolve it.
-/
structure ResolvableCompletionItemData extends CompletionItemData where
  /-- Position of the completion info that this completion item was created from. -/
  cPos : Nat
  id?  : Option CompletionIdentifier
  deriving FromJson, ToJson

private partial def consumeImplicitPrefix (e : Expr) (k : Expr → MetaM α) : MetaM α := do
  match e with
  | Expr.forallE n d b c =>
    -- We do not consume instance implicit arguments because the user probably wants be aware of this dependency
    if c == .implicit then
      Meta.withLocalDecl n c d fun arg =>
        consumeImplicitPrefix (b.instantiate1 arg) k
    else
      k e
  | _ => k e

/--
Fills the `CompletionItem.detail?` field of `item` using the pretty-printed type identified by `id`.
-/
def CompletionItem.resolve
    (item : CompletionItem)
    (id   : CompletionIdentifier)
    : MetaM CompletionItem := do
  let env ← getEnv
  let lctx ← getLCtx
  let mut item := item

  if item.detail?.isNone then
    let type? := match id with
      | .const declName =>
        env.find? declName |>.map ConstantInfo.type
      | .fvar id =>
        lctx.find? id |>.map LocalDecl.type
    let detail? ← type?.mapM fun type =>
      consumeImplicitPrefix type fun typeWithoutImplicits =>
        return toString (← Meta.ppExpr typeWithoutImplicits)
    item := { item with detail? := detail? }

  return item

end Lean.Lsp

namespace Lean.Server.Completion
open Lean.Lsp
open Elab

/--
Fills the `CompletionItem.detail?` field of `item` using the pretty-printed type identified by `id`
in the context found at `hoverPos` in `infoTree`.
-/
def resolveCompletionItem?
    (fileMap           : FileMap)
    (hoverPos          : String.Pos)
    (cmdStx            : Syntax)
    (infoTree          : InfoTree)
    (item              : CompletionItem)
    (id                : CompletionIdentifier)
    (completionInfoPos : Nat)
    : IO CompletionItem := do
  let completionInfos := findCompletionInfosAt fileMap hoverPos cmdStx infoTree
  let some i := completionInfos.get? completionInfoPos
    | return item
  i.ctx.runMetaM i.info.lctx (item.resolve id)

end Lean.Server.Completion
