module

public import Lean

/-!
This file tests that custom Verso docstring extensions work in `module`s. The `@[doc_role]`,
`@[doc_code_block]`, `@[doc_directive]`, and `@[doc_command]` attributes should:

1. Enforce that the underlying definition is `meta` (since it is used during elaboration).

2. Work correctly. In particular, they should generate the `getArgs` wrapper as `meta`.
-/

set_option doc.verso true

open Lean Doc Elab Term

@[doc_role]
meta def r (_ : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .empty

@[doc_code_block]
meta def c (s : StrLit) : DocM (Block ElabInline ElabBlock) :=
  pure (Block.code (s.getString.toList.reverse |> String.ofList))

@[doc_directive]
meta def d (s : TSyntaxArray `block) : DocM (Block ElabInline ElabBlock) := do
  .concat <$> s.reverse.mapM elabBlock

@[doc_command]
meta def cmd (_ : Ident) : DocM (Block ElabInline ElabBlock) := do
  return .empty

/-- Uses the custom role: {r}`role here` -/
def useRole := ()

open Lean Elab Command in
/-- info: Uses the custom role: -/
#guard_msgs in
#eval show CommandElabM Unit from do
  IO.print (← findDocString? (← getEnv) ``useRole).get!

/--
Uses the custom code block:

```c
hello
```
-/
def useCodeBlock := ()

open Lean Elab Command in
/--
info: Uses the custom code block:

```

olleh
```
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  IO.print (← findDocString? (← getEnv) ``useCodeBlock).get!

/--
Uses the custom directive:

:::d

text

:::
-/
def useDirective := ()

open Lean Elab Command in
/--
info: Uses the custom directive:

text
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  IO.print (← findDocString? (← getEnv) ``useDirective).get!

/--
Uses the custom command:

{cmd Foo}
-/
def useCommand := ()

open Lean Elab Command in
/-- info: Uses the custom command: -/
#guard_msgs in
#eval show CommandElabM Unit from do
  IO.print (← findDocString? (← getEnv) ``useCommand).get!

-- Each attribute should refuse to apply to a definition that is not `meta`, since the generated
-- `.getArgs` wrapper is invoked at elaboration time.

def notMetaRole (_ : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .empty

/-- error: `notMetaRole` must be marked `meta` to be used as a docstring role -/
#guard_msgs in
attribute [doc_role] notMetaRole

def notMetaCodeBlock (s : StrLit) : DocM (Block ElabInline ElabBlock) :=
  pure (Block.code s.getString)

/-- error: `notMetaCodeBlock` must be marked `meta` to be used as a docstring code block -/
#guard_msgs in
attribute [doc_code_block] notMetaCodeBlock

def notMetaDirective (s : TSyntaxArray `block) : DocM (Block ElabInline ElabBlock) := do
  .concat <$> s.mapM elabBlock

/-- error: `notMetaDirective` must be marked `meta` to be used as a docstring directive -/
#guard_msgs in
attribute [doc_directive] notMetaDirective

def notMetaCommand (_ : Ident) : DocM (Block ElabInline ElabBlock) := do
  return .empty

/-- error: `notMetaCommand` must be marked `meta` to be used as a docstring command -/
#guard_msgs in
attribute [doc_command] notMetaCommand

-- The generated `getArgs` wrapper should have the same public/private visibility as the
-- definition it wraps. A private wrapper for a public def would mean the role couldn't be
-- used from importing modules.

@[doc_role]
public meta def publicRole (_ : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .empty

@[doc_role]
meta def internalRole (_ : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .empty

-- Same again, but applying the attribute as a separate command rather than inline:
public meta def publicRole' (_ : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .empty
attribute [doc_role] publicRole'

meta def internalRole' (_ : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .empty
attribute [doc_role] internalRole'

/--
info: publicRole.getArgs       visible publicly: true
internalRole.getArgs    visible publicly: false
publicRole'.getArgs     visible publicly: true
internalRole'.getArgs   visible publicly: false
-/
#guard_msgs in
#eval show Lean.Elab.Command.CommandElabM Unit from withExporting do
  IO.println s!"publicRole.getArgs       visible publicly: {← hasConst ``publicRole.getArgs}"
  IO.println s!"internalRole.getArgs    visible publicly: {← hasConst ``internalRole.getArgs}"
  IO.println s!"publicRole'.getArgs     visible publicly: {← hasConst ``publicRole'.getArgs}"
  IO.println s!"internalRole'.getArgs   visible publicly: {← hasConst ``internalRole'.getArgs}"
