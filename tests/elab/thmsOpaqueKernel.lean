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
