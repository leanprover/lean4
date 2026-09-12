import Lean

set_option doc.verso true

/-!
Checks that a docstring extension may name the content it receives either as a string literal or as
the literal content token that the parser produces, and that inline and block content may be named
in either the `Lean.Doc.Syntax` encoding or the parser's. Each form receives the same content.

An extension may also take a parameter of the view's type, which is filled from the element being
elaborated rather than from the arguments.

The attribute checks the type a declaration names when it is applied, which happens in the compiler
that builds the declaration. Accepting both forms lets the interfaces move to the content types
after a stage0 update, in a separate step.
-/

open Lean Doc Elab Command

/-- Reports its content, taking it as a string literal. -/
@[doc_code_block]
def reportLit (content : StrLit) : DocM (Block ElabInline ElabBlock) :=
  return .para #[.text s!"lit: {content.getString}"]

/-- Reports its content, taking it as a code block token. -/
@[doc_code_block]
def reportBlock (content : VersoCodeBlock) : DocM (Block ElabInline ElabBlock) :=
  return .para #[.text s!"block: {content.getVersoCodeBlock}"]

/-- Takes a named argument as well, so that content is not the only parameter. -/
@[doc_code_block]
def reportBoth (label : String) (content : VersoCodeBlock) : DocM (Block ElabInline ElabBlock) :=
  return .para #[.text s!"{label}: {content.getVersoCodeBlock}"]

/-- Reports its content, taking it as an inline code token. -/
@[doc_role]
def roleBlock (content : TSyntaxArray `inline) : DocM (Inline ElabInline) :=
  return .concat (← content.mapM elabInline)

/--
Takes the role's view alongside its arguments and content. A parameter of the view's type is filled
from the element being elaborated, so the expander reads the role's own name without a view of it
from the reference itself.
-/
@[doc_role]
def roleView (label : String) (role : RoleView) (content : TSyntaxArray ``Parser.inline) :
    DocM (Inline ElabInline) :=
  return .concat <|
    #[.text s!"{label}/{role.name.getId} args={role.args.size}: "] ++
      (← content.mapM elabInline)

/-- Takes a directive's view, and its content in the parser's encoding. -/
@[doc_directive]
def directiveView (dir : DirectiveView) (content : TSyntaxArray ``Parser.block) :
    DocM (Block ElabInline ElabBlock) :=
  return .concat <|
    #[.para #[.text s!"directive {dir.name.getId} delimiter={dir.opener.getVersoDelimiter}"]] ++
      (← content.mapM elabBlock)

/-- Takes a code block's view alongside its content. -/
@[doc_code_block]
def codeBlockView (block : CodeBlockView) (content : VersoCodeBlock) :
    DocM (Block ElabInline ElabBlock) :=
  return .para
    #[.text s!"code block args={block.args.size}: {content.getVersoCodeBlock.trimAscii}"]

/-- Takes a block-level command's view. It has no content of its own. -/
@[doc_command]
def commandView (cmd : CommandView) : DocM (Block ElabInline ElabBlock) :=
  return .para #[.text s!"command {cmd.name.getId} args={cmd.args.size}"]

/-- A command may take no parameters at all, since it has neither content nor arguments. -/
@[doc_command]
def commandBare : DocM (Block ElabInline ElabBlock) :=
  return .para #[.text "bare command"]

/-!
Both content types elaborate, and each receives the text between the fences.
-/

/--
```reportLit
hello
```

```reportBlock
hello
```

```reportBoth "named"
hello
```

{roleView "seen"}[x]

:::directiveView
inside
:::

```codeBlockView
code
```

{commandView}

{commandBare}
-/
def documented := ()

/--
info: lit: hello


block: hello


named: hello


seen/roleView args=1: x

directive directiveView delimiter=:::

inside

code block args=0: code

command commandView args=0

bare command
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let some doc ← findDocString? (← getEnv) `documented | throwError "no docstring"
  IO.println doc.trimAscii

/-!
A declaration that names another type fails to elaborate, and the message names the types the
attribute accepts.
-/

/--
error: Expected type of last parameter to `reportWrong` to be one of `Lean.Syntax.StrLit`, `Lean.Doc.VersoCodeBlock` but got `Nat`
-/
#guard_msgs in
@[doc_code_block]
def reportWrong (content : Nat) : DocM (Block ElabInline ElabBlock) :=
  return .para #[.text s!"{content}"]

/-!
An extension's parameters are its arguments, then at most one view, then its content. A command
contains no further content, so its parameters stop at the view.
-/

/--
error: `roleTwoViews` takes the view of the element twice, as `here` and as `also`, but there can be at most one view.
-/
#guard_msgs in
@[doc_role]
def roleTwoViews (here : RoleView) (also : RoleView) (content : TSyntaxArray `inline) :
    DocM (Inline ElabInline) :=
  return .concat (← content.mapM elabInline)

/--
error: `roleArgAfterView` takes the argument `label` after the view `role`. Arguments must precede a view.
-/
#guard_msgs in
@[doc_role]
def roleArgAfterView (role : RoleView) (label : String) (content : TSyntaxArray `inline) :
    DocM (Inline ElabInline) :=
  return .concat (← content.mapM elabInline)

/--
error: `roleWrongView` takes `cmd : CommandView`, which is the view of a block-level command. Use `RoleView` instead.
-/
#guard_msgs in
@[doc_role]
def roleWrongView (cmd : CommandView) (content : TSyntaxArray `inline) :
    DocM (Inline ElabInline) :=
  return .concat (← content.mapM elabInline)


/-!
A suggestion provider may also name either type. Only a provider that names the literal content
token gets a generated adapter to convert the content.
-/

/-- Suggests nothing, taking its content as a string literal. -/
@[doc_code_suggestions]
def suggestFromLit (_code : StrLit) : DocM (Array CodeSuggestion) := return #[]

/-- Suggests nothing, taking its content as an inline code token. -/
@[doc_code_suggestions]
def suggestFromCode (_code : VersoCode) : DocM (Array CodeSuggestion) := return #[]

/-- Suggests nothing, taking its content as a code block token. -/
@[doc_code_block_suggestions]
def suggestBlockFromBlock (_code : VersoCodeBlock) : DocM (Array CodeBlockSuggestion) := return #[]

/--
info: suggestFromLit registered directly: true
suggestFromCode registered through an adapter: true
suggestBlockFromBlock registered through an adapter: true
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let env ← getEnv
  IO.println s!"suggestFromLit registered directly: {(env.find? `suggestFromLit.adapt).isNone}"
  IO.println
    s!"suggestFromCode registered through an adapter: {(env.find? `suggestFromCode.adapt).isSome}"
  IO.println s!"suggestBlockFromBlock registered through an adapter: \
    {(env.find? `suggestBlockFromBlock.adapt).isSome}"
