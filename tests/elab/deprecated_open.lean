/-!
Tests that `open NS (x)` and `open NS renaming x → y` report deprecated declarations, with a hint
to switch to the replacement relative to the opened namespace.
-/

set_option linter.deprecated true

namespace NS
def replacementDef : Nat := 1
@[deprecated NS.replacementDef (since := "2025-01-01")] def deprecatedDef : Nat := 1
namespace Inner
def replacementDef : Nat := 1
@[deprecated NS.Inner.replacementDef (since := "2025-01-01")] def deprecatedDef : Nat := 1
end Inner
end NS

namespace Other
@[deprecated NS.replacementDef (since := "2025-01-01")] def deprecatedDef : Nat := 1
end Other

/--
warning: `NS.deprecatedDef` has been deprecated: Use `NS.replacementDef` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
open NS (deprecatedDef) in
example := 0

/--
warning: `NS.deprecatedDef` has been deprecated: Use `NS.replacementDef` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
open NS renaming deprecatedDef → renamedDef in
example := 0

/--
warning: `NS.Inner.deprecatedDef` has been deprecated: Use `NS.Inner.replacementDef` instead

Hint: Replace the deprecated name:
  I̵n̵n̵e̵r̵.̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵I̲n̲n̲e̲r̲.̲r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
open NS (Inner.deprecatedDef) in
example := 0

-- The replacement is not in the opened namespace, so no hint is offered.
/--
warning: `Other.deprecatedDef` has been deprecated: Use `NS.replacementDef` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.deprecatedDef` to `NS.replacementDef x`).
-/
#guard_msgs in
open Other (deprecatedDef) in
example := 0

-- `open ... in` in terms and tactics
/--
warning: `NS.deprecatedDef` has been deprecated: Use `NS.replacementDef` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
example : Nat := open NS (deprecatedDef) in 0

/--
warning: `NS.deprecatedDef` has been deprecated: Use `NS.replacementDef` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
example : True := by open NS (deprecatedDef) in trivial

-- Exporting a deprecated declaration is not reported: it keeps the deprecated alias available until
-- it is removed.
namespace Exporting
#guard_msgs in
export NS (deprecatedDef)
end Exporting

-- Hiding a deprecated declaration is not a use.
#guard_msgs in
open NS hiding deprecatedDef in
example := 0

#guard_msgs in
open NS (replacementDef) in
example := 0
