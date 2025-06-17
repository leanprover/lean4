import Lean
/-!
# Testing that `delab.elabCheck` is functional
-/

open Lean Meta

/-!
Disabled, get kernel error.
-/
/--
error: (kernel) declaration type mismatch, 'ElabCheckTest1' has type
  Bool
but it is expected to have type
  Nat
-/
#guard_msgs in
set_option debug.elabCheck false in
#eval do
  addDecl <| .defnDecl {
    name := `ElabCheckTest1
    levelParams := []
    type := mkConst ``Nat
    value := mkConst ``Bool.true
    hints := .abbrev
    safety := .safe
  }

/-!
Enabled, get elaborator error
-/
/--
error: declaration `ElabCheckTest2` has type
  Bool : Type
but is expected to have type
  Nat : Type
-/
#guard_msgs in
set_option debug.elabCheck true in
#eval do
  addDecl <| .defnDecl {
    name := `ElabCheckTest2
    levelParams := []
    type := mkConst ``Nat
    value := mkConst ``Bool.true
    hints := .abbrev
    safety := .safe
  }

/-!
For theorems, disabling value checking gets kernel error.
-/
/--
error: (kernel) declaration type mismatch, 'ElabCheckTest4' has type
  Bool
but it is expected to have type
  True
-/
#guard_msgs in
set_option debug.elabCheck true in
set_option debug.elabCheck.theoremValues false in
#eval do
  addDecl <| .thmDecl {
    name := `ElabCheckTest4
    levelParams := []
    type := mkConst ``True
    value := mkConst ``Bool.true
  }

/-!
For theorems, enabling value checking gets elaborator error.
-/
/--
error: declaration `ElabCheckTest3` has type
  Bool : Type
but is expected to have type
  True : Prop
-/
#guard_msgs in
set_option debug.elabCheck true in
set_option debug.elabCheck.theoremValues true in
#eval do
  addDecl <| .thmDecl {
    name := `ElabCheckTest3
    levelParams := []
    type := mkConst ``True
    value := mkConst ``Bool.true
  }
