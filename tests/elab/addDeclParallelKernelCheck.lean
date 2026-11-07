import Lean

/-!
Kernel checks of asynchronously added declarations run in parallel: a declaration is added to the
kernel environment before it is checked. Check that kernel errors are still reported, and that
following declarations, including ones using the rejected declaration, are unaffected.
-/

open Lean Elab Command

/--
error: (kernel) declaration type mismatch, 'bad' has type
  True
but it is expected to have type
  False
-/
#guard_msgs in
run_cmd liftCoreM <| addDecl <| .thmDecl {
  name := `bad, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }

theorem usesBad : 1 = 2 := bad.elim

def good : Nat := 1

theorem good_eq : good = 1 := rfl

/--
error: (kernel) declaration type mismatch, 'bad2' has type
  True
but it is expected to have type
  False
-/
#guard_msgs in
run_cmd liftCoreM do
  addDecl <| .thmDecl {
    name := `ok, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro }
  addDecl <| .thmDecl {
    name := `bad2, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }
  addDecl <| .thmDecl {
    name := `ok2, levelParams := [], type := mkConst ``True, value := mkConst `ok }

/-- info: ok2 : True -/
#guard_msgs in
#check ok2

/-! With kernel diagnostics enabled, checks stay sequential so that their counters are kept. -/

def two : Nat := 2

set_option diagnostics true in
set_option diagnostics.threshold 0 in
/--
trace: [diag] Diagnostics
  [type_class] used instances (max: 2, num: 2):
    [type_class] Grind.CommRing.OfCommSemiring.instOfNatQ ↦ 2
    [type_class] instOfNatNat ↦ 1
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
---
trace: [diag] Diagnostics
  [reduction] unfolded declarations (max: 1, num: 2):
    [reduction] two ↦ 1
    [reduction] OfNat.ofNat ↦ 1
  [reduction] unfolded reducible declarations (max: 2, num: 2):
    [reduction] DecidableEq ↦ 2
    [reduction] Nat.decEq ↦ 1
  [type_class] used instances (max: 2, num: 3):
    [type_class] Grind.CommRing.OfCommSemiring.instOfNatQ ↦ 2
    [type_class] instDecidableEqNat ↦ 1
    [type_class] instOfNatNat ↦ 1
  [kernel] unfolded declarations (max: 2, num: 7):
    [kernel] OfNat.ofNat ↦ 2
    [kernel] DecidableEq ↦ 1
    [kernel] instDecidableEqNat ↦ 1
    [kernel] instOfNatNat ↦ 1
    [kernel] two ↦ 1
    [kernel] decide ↦ 1
    [kernel] Nat.decEq ↦ 1
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
theorem two_eq : two = 2 := by decide
