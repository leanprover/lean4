import Lean

/-!
Tests that Verso docstrings report deprecated constants named by `{name}`, as well as deprecated
roles, directives, and code blocks, and that the speculative elaboration behind code suggestions
does not report deprecated constants.
-/

set_option linter.deprecated true
set_option doc.verso true

open Lean Doc Elab

def replacementDef : Nat := 1
@[deprecated replacementDef (since := "2025-01-01")] def deprecatedDef : Nat := 1

/--
warning: `deprecatedDef` has been deprecated: Use `replacementDef` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
/-- See {name}`deprecatedDef`. -/
def seeName := 1

/--
warning: `deprecatedDef` has been deprecated: Use `replacementDef` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
/-- See {lean}`deprecatedDef`. -/
def seeLean := 1

/--
warning: Code element could be more specific.

Hint: Insert a role to document it:
  • {̲l̲e̲a̲n̲}̲`deprecatedDef`
  • {̲n̲a̲m̲e̲}̲`deprecatedDef`
  • Use the `lit` role:
    {̲l̲i̲t̲}̲`deprecatedDef`
    to mark the code as literal text and disable suggestions
-/
#guard_msgs in
/-- See `deprecatedDef`. -/
def seeCode := 1

@[doc_role] meta def replacementRole (_xs : TSyntaxArray ``Lean.Doc.Parser.inline) :
    DocM (Inline ElabInline) :=
  pure (.concat #[])
@[doc_role] meta def deprecatedRole (_xs : TSyntaxArray ``Lean.Doc.Parser.inline) :
    DocM (Inline ElabInline) :=
  pure (.concat #[])
attribute [deprecated replacementRole (since := "2025-01-01")] deprecatedRole

/--
warning: `deprecatedRole` has been deprecated: Use `replacementRole` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵R̵o̵l̵e̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲R̲o̲l̲e̲
-/
#guard_msgs in
/-- {deprecatedRole}`a` -/
def useRole := 1

@[doc_directive] meta def replacementDirective (_xs : TSyntaxArray ``Lean.Doc.Parser.block) :
    DocM (Block ElabInline ElabBlock) :=
  pure (.concat #[])
@[doc_directive] meta def deprecatedDirective (_xs : TSyntaxArray ``Lean.Doc.Parser.block) :
    DocM (Block ElabInline ElabBlock) :=
  pure (.concat #[])
attribute [deprecated replacementDirective (since := "2025-01-01")] deprecatedDirective

/--
warning: `deprecatedDirective` has been deprecated: Use `replacementDirective` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵i̵r̵e̵c̵t̵i̵v̵e̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲i̲r̲e̲c̲t̲i̲v̲e̲
-/
#guard_msgs in
/--
:::deprecatedDirective
a
:::
-/
def useDirective := 1

@[doc_code_block] meta def replacementCodeBlock (_content : VersoCodeBlock) :
    DocM (Block ElabInline ElabBlock) :=
  pure (.concat #[])
@[doc_code_block] meta def deprecatedCodeBlock (_content : VersoCodeBlock) :
    DocM (Block ElabInline ElabBlock) :=
  pure (.concat #[])
attribute [deprecated replacementCodeBlock (since := "2025-01-01")] deprecatedCodeBlock

/--
warning: `deprecatedCodeBlock` has been deprecated: Use `replacementCodeBlock` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵C̵o̵d̵e̵B̵l̵o̵c̵k̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲C̲o̲d̲e̲B̲l̲o̲c̲k̲
-/
#guard_msgs in
/--
```deprecatedCodeBlock
a
```
-/
def useCodeBlock := 1
