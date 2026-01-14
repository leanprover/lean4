import Lean.Elab.Command

set_option doc.verso true

/-!
# Verso Docstring Markdown Tests

This module tests the Markdown rendering of all the builtin Verso docstring operators.

Each section begins with a command that will fail when a new, untested operator is added.

## Helpers

-/

section
open Lean Elab Command Term

private def toMarkdown : VersoDocString → String
  | .mk bs ps => Doc.MarkdownM.run' do
      for b in bs do
        Doc.ToMarkdown.toMarkdown b
      for p in ps do
        Doc.ToMarkdown.toMarkdown p

private def manualRw (md : String) : String := md.replace manualRoot "$MANUAL_ROOT/"

elab "#verso_to_markdown " name:ident : command => do
  let env ← getEnv
  runTermElabM fun _ => do
    let declName ← realizeGlobalConstNoOverloadWithInfo name
    match (← findInternalDocString? env declName (includeBuiltin := true)) with
    | some (.inl ..) => throwError m!"`{.ofConstName declName}` has a Markdown docstring"
    | some (.inr verso) => logInfo (manualRw (toMarkdown verso))
    | none => throwError m!"`{.ofConstName declName}` has no docstring"

/-!
## Code Blocks
-/

/-- info: #[Lean.Doc.lean, Lean.Doc.leanTerm, Lean.Doc.output] -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let builtinBlocks ← Doc.builtinDocCodeBlocks.get
  let blockNames := builtinBlocks.keysArray |>.qsort (fun x y => x.toString < y.toString)
  IO.println blockNames

/--
```lean
example : codeblockTest 4 5 = 9 := by rfl
```
```leanTerm
codeblockTest 4 5
```
```lean (name := x)
#eval codeblockTest 4 5
```
```output x
9
```
-/
def codeblockTest (x y : Nat) := x + y

/--
info: ```
example : codeblockTest 4 5 = 9 := by rfl
```

```
codeblockTest 4 5
```

```
#eval codeblockTest 4 5
```

```
9
```
-/
#guard_msgs in
#verso_to_markdown codeblockTest

/-!
## Directives

There are no builtin directives, but should any be added, they must be tested.
-/

/-- info: #[] -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let builtinBlocks ← Doc.builtinDocDirectives.get
  let blockNames := builtinBlocks.keysArray |>.qsort (fun x y => x.toString < y.toString)
  IO.println blockNames

/-!
## Commands
-/

/-- info: #[Lean.Doc.open, Lean.Doc.set_option] -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let builtinBlocks ← Doc.builtinDocCommands.get
  let blockNames := builtinBlocks.keysArray |>.qsort (fun x y => x.toString < y.toString)
  IO.println blockNames

namespace X
def z := 5
end X

/--
None of these commands should appear in the output:

{open X}

{set_option pp.all true}

-/
def commandTests (x y : Nat) : Nat := x + y

/-- info: None of these commands should appear in the output: -/
#guard_msgs in
#verso_to_markdown commandTests

/-!
## Roles
-/

/--
info: Lean.Doc.assert
Lean.Doc.assert'
Lean.Doc.attr
Lean.Doc.conv
Lean.Doc.given
Lean.Doc.givenInstance
Lean.Doc.kw
Lean.Doc.kw!
Lean.Doc.kw?
Lean.Doc.lean
Lean.Doc.lit
Lean.Doc.manual
Lean.Doc.module
Lean.Doc.name
Lean.Doc.option
Lean.Doc.syntax
Lean.Doc.syntaxCat
Lean.Doc.tactic
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let builtinRoles ← Doc.builtinDocRoles.get
  let blockNames := builtinRoles.keysArray |>.qsort (fun x y => x.toString < y.toString)
  blockNames.forM (IO.println ·)

/--
Because {assert}`assertTests 2 4 = 6`, it must certainly be addition.
-/
def assertTests (x y : Nat) := x + y

/-- info: Because `assertTests 2 4 = 6`, it must certainly be addition\. -/
#guard_msgs in
#verso_to_markdown assertTests

-- assert' not tested here because it's for bootstrapping and doesn't work outside early Prelude

/--
The attribute {attr}`simp` registers a simp lemma. Use {attr}`@[simp]`.
-/
def attrTests (x y : Nat) := x + y

/-- info: The attribute `simp` registers a simp lemma\. Use `@[simp]`\. -/
#guard_msgs in
#verso_to_markdown attrTests

/-- The {conv}`fun` tactic -/
def convTests (x y : Nat) := x + y

/-- info: The `fun` tactic -/
#guard_msgs in
#verso_to_markdown convTests

/--
Invisible: {given -show}`m : Nat`

Visible:
 * For {given}`n`, {assert}`givenTests n n = n - n`.
 * For {given}`n, k : Nat`, {assert}`givenTests n k = n - k`.
 * For {given}`n, k`, {assert}`givenTests n k = n - k`.
 * For {given (type:="Nat")}`k`, {assert}`givenTests m k = m - k`.
-/
def givenTests (x y : Nat) : Nat := x - y

/--
{given -show}`α : Type, β : Type, γ : Type` {given -show}`x : α, y : α, z : α`
Invisible: {givenInstance -show}`Add α` {givenInstance -show}`addInst : Add β`

There is an {lean}`addInst : Add β` and an {lean}`inferInstance : Add α`, and {lean}`x + y + z`.

Visible: {givenInstance}`Add γ`&{givenInstance}`addInst : OfNat γ 5`

Check: {lean}`(5 : γ) + 5`

-/
def givenInstanceTests (x y : Nat) : Nat := x - y

/--
info:  ⏎
Invisible:  ⏎

There is an `addInst : Add β` and an `inferInstance : Add α`, and `x + y + z`\.

Visible: `Add γ`&`addInst : OfNat γ 5`

Check: `(5 : γ) + 5`
-/
#guard_msgs in
#verso_to_markdown givenInstanceTests

/--
info: Invisible: ⏎

Visible:

* For `n`, `givenTests n n = n - n`\.

* For `n`, `k : Nat`, `givenTests n k = n - k`\.

* For `n`, `k`, `givenTests n k = n - k`\.

* For `k`, `givenTests m k = m - k`\.
-/
#guard_msgs in
#verso_to_markdown givenTests


/--
info:

Hint: Specify the syntax kind:
  kw?̵ ̲(̲o̲f̲ ̲:̲=̲ ̲P̲a̲r̲s̲e̲r̲.̲T̲a̲c̲t̲i̲c̲.̲C̲o̲n̲v̲.̲f̲u̲n̲)̲
-/
#guard_msgs in
/--
* {kw (of := termIfThenElse)}`if`
* {kw! (of := Lean.Parser.Term.fun)}`fun`
* {kw?}`fun`
-/
def kwTests := ()

/--
info: * `if`

* `fun`

* `fun`
-/
#guard_msgs in
#verso_to_markdown kwTests

/-- {lit}`$ ls -l`-/
def litTests := ()

/-- info: `$ ls -l` -/
#guard_msgs in
#verso_to_markdown litTests

/--
1. {lean}`2 + 2`
2. {lean (type :="Int")}`2 + 2`
-/
def leanRoleTests := ()

/--
info: 1. `2 + 2`

2. `2 + 2`
-/
#guard_msgs in
#verso_to_markdown leanRoleTests

/--
Link: {manual section "bar"}[link text] and done and {manual errorExplanation "errorId"}[other link]
-/
def manualLinkTests := ()

/--
info: Link: [link text]($MANUAL_ROOT/find/?domain=Verso.Genre.Manual.section&name=bar) and done and [other link]($MANUAL_ROOT/find/?domain=Manual.errorExplanation&name=errorId)
-/
#guard_msgs in
#verso_to_markdown manualLinkTests

/--
{module -checked}`NoModule` and {module}`Init`
-/
def moduleTests := ()

/-- info: `NoModule` and `Init` -/
#guard_msgs in
#verso_to_markdown moduleTests

/--
Argument names:

{name}`x`{name}`z`{name (full := X.z)}`z`
-/
def nameTests (x y z : Nat) := x - y + z

-- IMPORTANT: This has zero-width spaces between the code inlines. When updating the file, make sure
-- they're present.
/--
info: Argument names:

`x`​`z`​`z`
-/
#guard_msgs in
#verso_to_markdown nameTests

/--
* {option}`pp.all`
* {option}`set_option pp.all true`
-/
def optionTests := ()

/--
info: * `pp.all`

* `set_option pp.all true`
-/
#guard_msgs in
#verso_to_markdown optionTests

set_option linter.unusedVariables false in
/--

Tests:
1. {syntaxCat}`term`
2. {syntax level}`$x + $y`

A level: {name}`x`
-/
def syntaxTests := ()

/--
info: Tests:

1. `term`

2. `$x + $y`

A level: `x`
-/
#guard_msgs in
#verso_to_markdown syntaxTests

/--
{tactic}`intros`
-/
def tacticTests := ()

/-- info: `intros` -/
#guard_msgs in
#verso_to_markdown tacticTests
