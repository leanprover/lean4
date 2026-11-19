/-!
Tests that the quotation precheck reports deprecated constants used with field notation at the
constant only, excluding the fields, and offers a hint that replaces only the constant.
-/

set_option linter.deprecated true

def replacementDef := 1
@[deprecated replacementDef (since := "2025-01-01")] def deprecatedDef := 1

/--
@ +1:40...53
warning: `deprecatedDef` has been deprecated: Use `replacementDef` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs (positions := true) in
macro "fieldDeprecatedDef" : term => ``(deprecatedDef.succ)

/--
@ +1:34...47
warning: `deprecatedDef` has been deprecated: Use `replacementDef` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs (positions := true) in
notation "fieldDeprecatedDef2" => deprecatedDef.succ.succ
