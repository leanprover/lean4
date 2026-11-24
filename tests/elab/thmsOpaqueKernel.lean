import Lean.Elab.Command

/-!
# Theorems are opaque to the kernel as well

Follow-up to #12973: the kernel used to still delta-reduce theorems, while the elaborator does not.
-/

open Lean

theorem thmTrue : True := True.intro
def defTrue : True := True.intro

def kernelWhnf (n : Name) : MetaM Expr := do
  ofExceptKernelException <| Kernel.whnf (← getEnv) {} (mkConst n)

/-- info: thmTrue -/
#guard_msgs in
run_meta logInfo (← kernelWhnf ``thmTrue)

/-- info: True.intro -/
#guard_msgs in
run_meta logInfo (← kernelWhnf ``defTrue)

/-!
The kernel also agrees with the elaborator on recursor applications whose major premise is a
theorem. `Q` large-eliminates, but is neither K-like nor a structure, so reducing `Q.rec` would
require unfolding `qZero`.
-/

inductive Q : Nat → Prop
  | mk : True → Q 0

theorem qZero : Q 0 := .mk trivial

noncomputable def qVal : Nat := Q.rec (motive := fun _ _ => Nat) (fun _ => 37) qZero

/--
error: Type mismatch
  Eq.refl qVal
has type
  qVal = qVal
but is expected to have type
  qVal = 37
-/
#guard_msgs in
example : qVal = 37 := Eq.refl qVal

/--
error: (kernel) declaration type mismatch, 'kernelReduces' has type
  qVal = qVal
but it is expected to have type
  qVal = 37
-/
#guard_msgs in
run_meta
  addDecl (.thmDecl {
    name := `kernelReduces, levelParams := [],
    type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkConst ``qVal) (mkNatLit 37),
    value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkConst ``qVal),
    all := [`kernelReduces] })
