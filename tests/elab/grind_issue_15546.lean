module

/-!
Regression test for #15546: `grind` must compare instances at `.implicit` transparency,
so that `@[implicit_reducible]` definitions wrapping an instance unfold during instance
canonicalization. Previously the comparison ran at `.instances` and `inst2 =?= inst1` failed.
-/

class C : Type where
  x : Nat

instance inst1 : C where
  x := 0

@[implicit_reducible]
def inst2 := inst1

#guard_msgs in -- Should not produce any issues
set_option trace.sym.issues true in
example (a : Nat) (h : inst1.x = a) : inst2.x = a := by
  grind

/-- Instance nested inside an implicit-reducible definition used as an explicit instance argument. -/
@[implicit_reducible]
def instAdd' : Add Nat := inferInstance

#guard_msgs in -- Should not produce any issues
set_option trace.sym.issues true in
example (a b : Nat) (h : @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAdd') a b = 1) : a + b = 1 := by
  grind
