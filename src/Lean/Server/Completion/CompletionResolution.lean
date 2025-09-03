/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Marc Huisinga
-/
module

prelude
public import Lean.Server.Completion.CompletionItemData
public import Lean.Server.Completion.CompletionInfoSelection
public import Lean.Linter.Deprecated

public section

namespace Lean.Lsp

/--
Identifier that is sent from the server to the client as part of the `CompletionItem.data?` field.
Needed to resolve the `CompletionItem` when the client sends a `completionItem/resolve` request
for that item, again containing the `data?` field provided by the server.
-/
inductive CompletionIdentifier where
  | const (declName : Name)
  | fvar (id : FVarId)

instance : ToJson CompletionIdentifier where
  toJson
  | .const declName =>
    .str s!"c{toString declName}"
  | .fvar id =>
    .str s!"f{toString id.name}"

instance : FromJson CompletionIdentifier where
  fromJson?
    | .str s =>
      let c := s.get 0
      if c == 'c' then
        let declName := s.extract ⟨1⟩ s.endPos |>.toName
        .ok <| .const declName
      else if c == 'f' then
        let id := ⟨s.extract ⟨1⟩ s.endPos |>.toName⟩
        .ok <| .fvar id
      else
        .error "Expected string with prefix `c` or `f` in `FromJson` instance of `CompletionIdentifier`."
    | _ => .error "Expected string in `FromJson` instance of `CompletionIdentifier`."

/--
`CompletionItemData` that contains additional information to identify the item
in order to resolve it.
-/
structure ResolvableCompletionItemData extends CompletionItemData where
  /-- Position of the completion info that this completion item was created from. -/
  cPos : Nat
  id?  : Option CompletionIdentifier

-- Compressed `ToJson`/`FromJson` instances since
instance : ToJson ResolvableCompletionItemData where
  toJson d :=
    let arr : Array Json := #[
      toJson d.mod,
      d.pos.line,
      d.pos.character,
      d.cPos
    ]
    Json.arr <|
      match d.id? with
      | some id => arr.push (toJson id)
      | none => arr

instance : FromJson ResolvableCompletionItemData where
  fromJson?
    | .arr elems => do
      if elems.size < 4 then
        .error "Expected array of size 4 in `FromJson` instance of `ResolvableCompletionItemData"
      let mod : Name ← fromJson? elems[0]!
      let line : Nat ← fromJson? elems[1]!
      let character : Nat ← fromJson? elems[2]!
      let cPos : Nat ← fromJson? elems[3]!
      let id? : Option CompletionIdentifier ← elems[4]?.mapM fromJson?
      let pos := { line, character }
      return {
        mod
        pos
        cPos
        id?
      }
    | _ => .error "Expected array in `FromJson` instance of `ResolvableCompletionItemData`"

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
    (hoverPos          : String.Pos)
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
