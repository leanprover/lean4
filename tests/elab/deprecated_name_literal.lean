import Lean

/-!
Tests that resolved name literals ``` ``x ``` and the patterns of `match_expr` report deprecated
constants.
-/

set_option linter.deprecated true

open Lean

def replacementDef (n : Nat) : Nat := n + 1
@[deprecated replacementDef (since := "2025-01-01")] def deprecatedDef (n : Nat) : Nat := n + 1

/--
warning: `deprecatedDef` has been deprecated: Use `replacementDef` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
example : Name := ``deprecatedDef

/--
warning: `deprecatedDef` has been deprecated: Use `replacementDef` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
def matchDeprecatedDef (e : Expr) : Option Expr :=
  match_expr e with
  | deprecatedDef a => some a
  | _ => none

/--
warning: `deprecatedDef` has been deprecated: Use `replacementDef` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
def matchDeprecatedDefM (e : Expr) : MetaM (Option Expr) :=
  match_expr e with
  | deprecatedDef a => return some a
  | _ => return none

-- Unresolved name literals are not checked.
#guard_msgs in
example : Name := `deprecatedDef

#guard_msgs in
example : Name := ``replacementDef
