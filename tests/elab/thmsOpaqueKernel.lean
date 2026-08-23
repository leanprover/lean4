import Lean.Elab.Command

/-!
# Theorems are opaque to the kernel as well

Follow-up to #12973: the kernel used to still delta-reduce theorems, so a term could be
accepted by the kernel that the elaborator refuses to check.
-/

open Lean

theorem accZero : Acc (fun a b : Nat => a < b) 0 := .intro _ (fun _ h => absurd h (by omega))

def accVal : Nat := Acc.rec (motive := fun _ _ => Nat) (fun _ _ _ => 37) accZero

-- The elaborator does not unfold `accZero`, so this does not reduce
/--
error: Type mismatch
  Eq.refl accVal
has type
  accVal = accVal
but is expected to have type
  accVal = 37
-/
#guard_msgs in
example : accVal = 37 := Eq.refl accVal

-- ... and neither does the kernel
/--
error: (kernel) declaration type mismatch, 'kernelReduces' has type
  accVal = accVal
but it is expected to have type
  accVal = 37
-/
#guard_msgs in
run_meta
  addDecl (.thmDecl {
    name := `kernelReduces, levelParams := [],
    type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkConst ``accVal) (mkNatLit 37),
    value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkConst ``accVal),
    all := [`kernelReduces] })

-- When the proof is a `def`, reduction still works, in the elaborator and in the kernel
def accZero' : Acc (fun a b : Nat => a < b) 0 := .intro _ (fun _ h => absurd h (by omega))

def accVal' : Nat := Acc.rec (motive := fun _ _ => Nat) (fun _ _ _ => 37) accZero'

example : accVal' = 37 := rfl
