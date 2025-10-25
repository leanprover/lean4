/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Marc Huisinga
-/
module

prelude
public import Lean.Data.Lsp
public import Lean.Server.Completion.CompletionInfoSelection
public import Lean.Linter.Deprecated

public section

namespace Lean.Lsp

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

  if item.documentation?.isNone then
    let docStringPrefix? := Id.run do
      let .const declName := id
        | none
      let some param := Linter.deprecatedAttr.getParam? env declName
        | none
      let docstringPrefix :=
        if let some text := param.text? then
          text
        else if let some newName := param.newName? then
          s!"`{declName}` has been deprecated, use `{newName}` instead."
        else
          s!"`{declName}` has been deprecated."
      some docstringPrefix
    let docString? ← do
      let .const declName := id
        | pure none
      findDocString? env declName
    let doc? := do
      let docValue ←
        match docStringPrefix?, docString? with
        | none,                 none           => none
        | some docStringPrefix, none           => docStringPrefix
        | none,                 docString      => docString
        | some docStringPrefix, some docString => s!"{docStringPrefix}\n\n{docString}"
      pure { value := docValue , kind := MarkupKind.markdown : MarkupContent }
    item := { item with documentation? := doc? }

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
    (hoverPos          : String.Pos.Raw)
    (cmdStx            : Syntax)
    (infoTree          : InfoTree)
    (item              : CompletionItem)
    (id                : CompletionIdentifier)
    (completionInfoPos : Nat)
    : IO CompletionItem := do
  let (completionInfos, _) := findCompletionInfosAt fileMap hoverPos cmdStx infoTree
  let some i := completionInfos[completionInfoPos]?
    | return item
  i.ctx.runMetaM i.info.lctx (item.resolve id)

end Lean.Server.Completion
