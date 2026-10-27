import Lean

/-!
Tests that the quotation precheck of notations and checked quotations reports deprecated
constants and syntax where the quotation mentions them, not only where the notation is used.
-/

open Lean

set_option linter.deprecated true
set_option linter.deprecated.syntax true

def newConst := 1

@[deprecated newConst (since := "2026-10-22")]
def oldConst := 1

/--
warning: `oldConst` has been deprecated: Use `newConst` instead

Hint: Replace the deprecated name:
  o̵l̵d̵n̲e̲w̲Const
-/
#guard_msgs in
notation "notationOld" => oldConst

-- Uses of the notation are still reported.
/-- warning: `oldConst` has been deprecated: Use `newConst` instead -/
#guard_msgs in
example : Nat := notationOld

/--
warning: `oldConst` has been deprecated: Use `newConst` instead

Hint: Replace the deprecated name:
  o̵l̵d̵n̲e̲w̲Const
-/
#guard_msgs in
macro "macroOld " x:term:max : term => ``(oldConst + $x)

/--
warning: `oldConst` has been deprecated: Use `newConst` instead

Hint: Replace the deprecated name:
  o̵l̵d̵n̲e̲w̲Const
-/
#guard_msgs in
infixl:65 " +' " => oldConst

/--
warning: `oldConst` has been deprecated: Use `newConst` instead

Hint: Replace the deprecated name:
  o̵l̵d̵n̲e̲w̲Const
-/
#guard_msgs in
macro "explicitOld" : term => ``(@oldConst)

-- Field notation on a deprecated constant
/-- warning: `oldConst` has been deprecated: Use `newConst` instead -/
#guard_msgs in
macro "fieldOld" : term => ``(oldConst.succ)

-- Single backtick quotations are not prechecked.
#guard_msgs in
macro "uncheckedOld" : term => `(oldConst)

#guard_msgs in
set_option quotPrecheck false in
macro "noPrecheckOld" : term => ``(oldConst)

#guard_msgs in
set_option linter.deprecated false in
macro "lintOffOld" : term => ``(oldConst)

#guard_msgs in
@[deprecated "use `newConst`" (since := "2026-10-22")]
def mkOld : MacroM Term := ``(oldConst)

-- Deprecated declarations do not report deprecated syntax in quotations either.
syntax (name := oldSyntax) "old_syntax" : term
macro_rules | `(old_syntax) => `(newConst)
deprecated_syntax oldSyntax "use `newConst` instead" (since := "2026-10-22")

/--
warning: quotation uses deprecated syntax 'oldSyntax': use `newConst` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
def mkOldSyntax : MacroM Term := ``(old_syntax)

#guard_msgs in
@[deprecated "use `newConst`" (since := "2026-10-22")]
def mkOldSyntaxDeprecated : MacroM Term := ``(old_syntax)

-- Variables bound in the quotation shadow deprecated constants.
@[deprecated "" (since := "2026-10-22")]
def l := 1

#guard_msgs in
macro "boundOld" : term => ``(fun (oldConst : Nat) => oldConst + 1)

#guard_msgs in
macro "boundField" : term => ``(fun (l : List Nat) => l.length)

-- Section variables shadow deprecated constants in notations used inside the section.
namespace SectionVars

def newX := 1

@[deprecated newX (since := "2026-10-22")]
def x := 1

section
variable (x : Nat)

#guard_msgs in
local notation "localX" => x

#guard_msgs in
def useLocalX := localX

end

end SectionVars

-- Overloaded identifiers are reported once elaborating the notation picks a constant.
namespace A
@[deprecated "" (since := "2026-10-22")]
def overloaded : Nat := 1
end A

namespace B
def overloaded : String := ""
end B

open A B in
#guard_msgs in
macro "overloaded" : term => ``(overloaded)

/-- warning: `A.overloaded` has been deprecated: -/
#guard_msgs in
example : Nat := overloaded

#guard_msgs in
example : String := overloaded

-- Identifiers produced by macros used in the quotation are reported where the result is elaborated.
macro "addOld " x:term:max : term => do
  let old := mkIdentFrom (← getRef) ``oldConst
  ``($old + $x)

#guard_msgs in
macro "expandsToOld" : term => ``(addOld newConst)

/-- warning: `oldConst` has been deprecated: Use `newConst` instead -/
#guard_msgs in
example : Nat := expandsToOld
