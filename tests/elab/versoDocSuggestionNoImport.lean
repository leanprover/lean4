set_option doc.verso true

/-!
When a builtin role name like {lit}`lit` is shadowed by a user definition, the suggestion should use
the qualified name {lit}`Lean.Doc.lit`. This test checks that this also works when there are no
imports.
-/

namespace ShadowedBuiltin
def lit := Nat  -- Shadow the builtin 'lit' role

/--
warning: Code element could be more specific.

Hint: Insert a role to document it:
  • {̲g̲i̲v̲e̲n̲}̲`test`
  • Use the `lit` role:
    {̲L̲e̲a̲n̲.̲D̲o̲c̲.̲l̲i̲t̲}̲`test`
    to mark the code as literal text and disable suggestions
-/
#guard_msgs in
/--
`test`
-/
def testShadowedLit := 0

-- Verify that {Lean.Doc.lit} works when lit is shadowed
#guard_msgs in
/-- {Lean.Doc.lit}`qualified works` -/
def testQualifiedLit := 1

open Lean
-- Verify that {Doc.lit} works when lit is shadowed and Lean is not imported
#guard_msgs in
/-- {Doc.lit}`qualified works` -/
def testQualifiedLit2 := 1


-- {lit} fails when shadowed
/--
error: `lit : Type` is not registered as a a role

Hint: `lit` shadows a role. Use the full name of the shadowed role:
  L̲e̲a̲n̲.̲D̲o̲c̲.̲lit
-/
#guard_msgs in
/-- {lit}`broken` -/
def testBrokenLit := 0

end ShadowedBuiltin
