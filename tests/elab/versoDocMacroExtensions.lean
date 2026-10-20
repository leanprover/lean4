import Lean

/-!
Checks that docstring extensions behave the same in macro-generated declarations as in hand-written
ones.

An extension that reparses its content reads it from the source file when the content's position is
canonical, and from the decoded string otherwise. Macro-generated syntax has non-canonical
positions, because its positions point at the macro's use site instead of at the content. An
extension that loses that distinction therefore reparses the wrong region. Nothing reports that
failure: the docstring still elaborates, to the wrong thing.

Each extension below therefore appears twice, once through a macro and once directly. The two
elaborated docstrings must be equal.
-/

set_option doc.verso true
-- These docstrings exercise the extensions, not the suggestions.
set_option doc.verso.suggestions false

open Lean Elab Command

-- Custom elements contain `Dynamic`s, which cannot be compared, so `sameDocs` compares the
-- rendered form. That form shows every decoded string, which is what these extensions get wrong.
deriving instance Repr for VersoDocString

/-- Elaborated docstrings for two declarations must agree. -/
def sameDocs (what : String) (viaMacro direct : Name) : CommandElabM Unit := do
  let get (x : Name) : CommandElabM (Option VersoDocString) := do
    match ← findInternalDocString? (← getEnv) x with
    | some (.inr v) => return some v
    | some (.inl _) => throwError m!"`{.ofConstName x}` has a Markdown docstring, not a Verso one"
    | none => throwError m!"`{.ofConstName x}` has no docstring"
  match ← get viaMacro, ← get direct with
  | some a, some b =>
    let a := toString (repr a)
    let b := toString (repr b)
    if a == b then IO.println s!"{what}: agree"
    else IO.println s!"{what}: DIFFER\n  via macro: {a}\n  direct:    {b}"
  | _, _ => throwError "missing docstring"

section Roles

/--
A macro whose generated declaration has a docstring using the extensions that reparse their
content.
-/
-- This docstring stands at the same indentation as the one below, so that the two differ only in
-- how they reach the elaborator.
macro "docWithRoles" nm:ident : command => `(
/-- Uses {lean}`Nat.succ`, {name}`Nat.succ`, {lit}`literal`, {tactic}`rfl`, {conv}`rfl`, {option}`pp.all`, {attr}`simp`, {module}`Init`, and {syntaxCat}`term`. -/
def $nm := 0)

docWithRoles rolesViaMacro

/-- Uses {lean}`Nat.succ`, {name}`Nat.succ`, {lit}`literal`, {tactic}`rfl`, {conv}`rfl`, {option}`pp.all`, {attr}`simp`, {module}`Init`, and {syntaxCat}`term`. -/
def rolesDirect := 0

/-- info: roles: agree -/
#guard_msgs in
#eval sameDocs "roles" ``rolesViaMacro ``rolesDirect

end Roles

section CodeBlocks

/-- A macro whose generated declaration has a docstring using code blocks. -/
macro "docWithCode" nm:ident : command => `(
/--
A code block:
```lean
example : Nat := 0
```
And a term:
```leanTerm
Nat.succ 0
```
-/
def $nm := 0)

docWithCode codeViaMacro

/--
A code block:
```lean
example : Nat := 0
```
And a term:
```leanTerm
Nat.succ 0
```
-/
def codeDirect := 0

/-- info: code blocks: agree -/
#guard_msgs in
#eval sameDocs "code blocks" ``codeViaMacro ``codeDirect

end CodeBlocks

section Structure

/-- A macro whose generated declaration has a docstring using the block constructs. -/
macro "docWithStructure" nm:ident : command => `(
/--
A paragraph with _emphasis_, *bold*, `code`, $`x + 1`, and a [link](https://example.com).

* A list item
* Another item

1. Numbered
2. Also numbered

> A quotation

# A header

Text under the header.
-/
def $nm := 0)

docWithStructure structureViaMacro

/--
A paragraph with _emphasis_, *bold*, `code`, $`x + 1`, and a [link](https://example.com).

* A list item
* Another item

1. Numbered
2. Also numbered

> A quotation

# A header

Text under the header.
-/
def structureDirect := 0

/-- info: structure: agree -/
#guard_msgs in
#eval sameDocs "structure" ``structureViaMacro ``structureDirect

end Structure
