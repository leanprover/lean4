import Lean

open Lean Doc Elab Command
open scoped Lean.Doc.Syntax

/-!
Tests user-extensible Markdown rendering of docstring elements, without the module system.

This mirrors `versoDocCustomRenderer.lean` but in a non-module file, where roles and renderers need
not be `meta`. A user-defined docstring role saves a custom data element, and a renderer registered
with `@[doc_inline_md]` controls how that element renders to Markdown. The renderer is written
against the custom element type directly (`InlineMdRendererOf X`); the attribute generates the
`Dynamic`-decoding wrapper. Elements whose type has no registered renderer fall back to rendering
their fallback content.
-/

set_option doc.verso true
set_option doc.verso.suggestions false

/--
Renders a declaration's docstring to Markdown, as the language server would. The current namespace
and open declarations are passed through, so renderers that shorten names see this scope.
-/
elab "#render_doc " name:ident : command => do
  let env ← getEnv
  let currNamespace ← getCurrNamespace
  let openDecls ← getOpenDecls
  runTermElabM fun _ => do
    let declName ← realizeGlobalConstNoOverloadWithInfo name
    match (← findDocString? env declName (currNamespace := currNamespace) (openDecls := openDecls)) with
    | some s => logInfo s
    | none => throwError m!"`{MessageData.ofConstName declName}` has no docstring"

/-- Reads a single code inline and resolves it to a global constant. -/
def codeTargetName (xs : TSyntaxArray `inline) : DocM Name :=
  match xs with
  | #[stx] => match stx with
    | `(inline|code($s)) => realizeGlobalConstNoOverloadWithInfo (mkIdentFrom s s.getString.toName)
    | _ => throwErrorAt stx "expected a code argument"
  | _ => throwError "expected one code argument"

-- A renderer that includes another declaration's docstring at render time.

/-- A request to include another declaration's docstring. -/
structure IncludeDoc where
  /-- The declaration whose docstring should be included. -/
  target : Name
deriving TypeName

/-- Includes another declaration's docstring. The target is looked up when rendering to Markdown. -/
@[doc_role]
def include_docstring (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .custom (IncludeDoc.mk (← codeTargetName xs)) #[]

/-- The renderer receives the decoded `IncludeDoc` directly, never a `Dynamic`. -/
@[doc_inline_md]
def includeRender : InlineMdRendererOf IncludeDoc := fun _go data _content => do
  match (← (findInternalDocString? (← (getEnv : CoreM _)) data.target : IO _)) with
  | some (.inl str) => return ((str.split '\n').map (·.copy)).toArray
  | some (.inr verso) => ToMarkdown.toMarkdown verso
  | none => return #[]

/-- Hello from Foo. -/
def Foo : Nat := 0

/-- {include_docstring}`Foo` -/
def Bar : Nat := 1

/-- info: Hello from Foo. -/
#guard_msgs in
#render_doc Foo

/-- info: Hello from Foo. -/
#guard_msgs in
#render_doc Bar

-- An element whose type has no registered renderer renders its fallback content.

/-- A custom element with no registered renderer. -/
structure Unrendered where
deriving TypeName

/-- Wraps its content in a custom element that has no renderer. -/
@[doc_role]
def passthrough (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .custom Unrendered.mk (← xs.mapM elabInline)

/-- Fallback shows {passthrough}[the content] here. -/
def Baz : Nat := 2

/-- info: Fallback shows the content here. -/
#guard_msgs in
#render_doc Baz

-- A renderer that exceeds its heartbeat budget degrades to rendering the element's fallback
-- content, and surrounding content still renders.

/-- A custom element whose renderer never terminates. -/
structure Slow where
deriving TypeName

/-- Wraps its content in an element rendered by a non-terminating renderer. -/
@[doc_role]
def slow (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .custom Slow.mk (← xs.mapM elabInline)

@[doc_inline_md]
def slowRender : InlineMdRendererOf Slow := fun _go _data _content => do
  for _ in [0:100000000] do
    Lean.Core.checkSystem "slowRender"
  return #["unreached"]

/-- Before {slow}[the content] after. -/
def Slowest : Nat := 3

/-- info: Before the content after. -/
#guard_msgs in
#render_doc Slowest

-- A renderer that shortens a constant's name to the minimal form valid in the render scope,
-- computed at render time from the current namespace and open declarations.

/-- A reference to a constant, rendered with the shortest name valid in the render scope. -/
structure QualName where
  /-- The referenced constant. -/
  target : Name
deriving TypeName

/-- References a constant by its shortest name valid where the docstring is rendered. -/
@[doc_role]
def qualName (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .custom (QualName.mk (← codeTargetName xs)) #[]

@[doc_inline_md]
def qualNameRender : InlineMdRendererOf QualName := fun _go data _content => do
  return #[s!"`{← unresolveNameGlobal data.target}`"]

namespace Demo
/-- A demo constant in a namespace. -/
def widget : Nat := 0
end Demo

/-- Refers to {qualName}`Demo.widget`. -/
def UsesQualName : Nat := 1

/-- info: Refers to `Demo.widget`. -/
#guard_msgs in
#render_doc UsesQualName

/-- info: Refers to `widget`. -/
#guard_msgs in
open Demo in
#render_doc UsesQualName

-- Completion item documentation renders in the completion's scope, like hover.

open Demo in
/-- info: Refers to `widget`. -/
#guard_msgs in
#eval show Lean.Elab.Term.TermElabM Unit from do
  let item ← (Lean.Lsp.CompletionItem.resolve { label := "x" } (.const ``UsesQualName) : MetaM _)
  IO.println ((item.documentation?.map (·.value)).getD "<none>")

-- A renderer that pretty-prints a declaration's signature at render time (a `MetaM` escalation).
-- Rendering uses constant, default pretty-printing options so docstrings render canonically.

/-- A reference to a declaration, rendered as its signature. -/
structure SigData where
  /-- The referenced declaration. -/
  target : Name
deriving TypeName

/-- Shows a declaration's signature, pretty-printed when the docstring is rendered. -/
@[doc_role]
def sig (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .custom (SigData.mk (← codeTargetName xs)) #[]

@[doc_inline_md]
def sigRender : InlineMdRendererOf SigData := fun _go data _content => do
  let fmt ← (Lean.PrettyPrinter.ppSignature data.target).run'
  return #[s!"`{fmt.fmt.pretty (width := 100)}`"]

/-- Has signature {sig}`Foo`. -/
def UsesSig : Nat := 2

/-- info: Has signature `Foo : Nat`. -/
#guard_msgs in
#render_doc UsesSig

-- A renderer that fails after rendering some of its content must not leak that partial state (here,
-- footnotes) into the fallback rendering.

/-- A custom element whose renderer renders its content and then fails. -/
structure Leaky where
deriving TypeName

/-- Wraps its content in an element whose renderer fails after rendering the content. -/
@[doc_role]
def leaky (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .custom Leaky.mk (← xs.mapM elabInline)

@[doc_inline_md]
def leakyRender : InlineMdRendererOf Leaky := fun go _data content => do
  let _ ← content.mapM go
  throwError "renderer failed"

/--
Note {leaky}[see[^fn]] here.

[^fn]: the body
-/
def LeakyDoc : Nat := 4

/--
info: Note see[^fn] here.

[^fn]:the body
-/
#guard_msgs in
#render_doc LeakyDoc

-- A renderer declared against a reducible alias of the element type still matches elements stored
-- under the underlying type's name. The registry key is the `TypeName`-canonical name, not the
-- syntactic head of the renderer's declared type.

/-- The underlying custom element type. -/
structure Aliased where
  /-- The text to render. -/
  msg : String
deriving TypeName

/-- A reducible alias of the element type. -/
abbrev AliasedSyn := Aliased

/-- Stores an `Aliased` element, with distinct fallback content. -/
@[doc_role]
def aliased (_xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .custom (Aliased.mk "rendered via alias") #[.text "fallback"]

/-- The renderer is declared against the alias rather than `Aliased` itself. -/
@[doc_inline_md]
def aliasedRender : InlineMdRendererOf AliasedSyn := fun _go data _content => do
  return #[data.msg]

/-- Shows {aliased}[x]. -/
def UsesAlias : Nat := 5

/-- info: Shows rendered via alias. -/
#guard_msgs in
#render_doc UsesAlias

-- Block elements can have custom Markdown renderers too, registered with `@[doc_block_md]`. The
-- renderer receives both inline and block render callbacks.

/-- A custom block element. -/
structure Banner where
deriving TypeName

/-- A directive that wraps its blocks in a custom element. -/
@[doc_directive]
def banner (xs : TSyntaxArray `block) : DocM (Block ElabInline ElabBlock) := do
  return .custom Banner.mk (← xs.mapM elabBlock)

/-- The renderer brackets the rendered block content. -/
@[doc_block_md]
def bannerRender : BlockMdRendererOf Banner := fun _goI goB _data content => do
  let inner ← content.mapM goB
  return #["<<<"] ++ joinBlocks inner ++ #[">>>"]

/--
Intro.

:::banner
The body.
:::
-/
def UsesBanner : Nat := 6

/--
info: Intro.

<<<
The body.
>>>
-/
#guard_msgs in
#render_doc UsesBanner

-- A block element whose type has no registered renderer renders its fallback content.

/-- A custom block element with no registered renderer. -/
structure PlainBlock where
deriving TypeName

/-- A directive whose element type has no Markdown renderer. -/
@[doc_directive]
def plainBlock (xs : TSyntaxArray `block) : DocM (Block ElabInline ElabBlock) := do
  return .custom PlainBlock.mk (← xs.mapM elabBlock)

/--
:::plainBlock
Just the content.
:::
-/
def UsesPlainBlock : Nat := 7

/-- info: Just the content. -/
#guard_msgs in
#render_doc UsesPlainBlock

-- A block renderer that exceeds its heartbeat budget degrades to rendering the fallback content.

/-- A custom block element whose renderer never terminates. -/
structure SlowBlock where
deriving TypeName

/-- A directive rendered by a non-terminating renderer. -/
@[doc_directive]
def slowBlock (xs : TSyntaxArray `block) : DocM (Block ElabInline ElabBlock) := do
  return .custom SlowBlock.mk (← xs.mapM elabBlock)

@[doc_block_md]
def slowBlockRender : BlockMdRendererOf SlowBlock := fun _goI _goB _data _content => do
  for _ in [0:100000000] do
    Lean.Core.checkSystem "slowBlockRender"
  return #["unreached"]

/--
:::slowBlock
Fallback body.
:::
-/
def UsesSlowBlock : Nat := 8

/-- info: Fallback body. -/
#guard_msgs in
#render_doc UsesSlowBlock

-- Error messages.

/-- A custom element type with no `TypeName` instance. -/
structure NoTypeName where
  x : Nat

/--
error: the custom element type
  NoTypeName
of `badRenderer` needs a `TypeName` instance.

Hint: Add `deriving TypeName`
-/
#guard_msgs in
@[doc_inline_md]
def badRenderer : InlineMdRendererOf NoTypeName := fun _go _data _content => return #[]

/--
error: `wrongType` must have type `InlineMdRendererOf X` for custom elements of type `X`
-/
#guard_msgs in
@[doc_inline_md]
def wrongType : Nat := 5
