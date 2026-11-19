import Lean
/-!
Constants created by a realization nested in another realization are type checked by the kernel
exactly once: when the result of the outermost realization is added to the environment that
requested it. In particular, an ill-typed constant is still rejected, and the error is reported once.
-/
open Lean Meta

/-- Adds the theorem `name : type := value`. -/
def addThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| .thmDecl { name, levelParams := [], type, value }

/-- Returns `true` if `name` is in the kernel environment. -/
def inKernelEnv (name : Name) : MetaM Bool :=
  return ((← getEnv).toKernelEnv.find? name).isSome

/-! Well-typed theorems created at depths 1, 2 and 3 are added to the kernel environment. -/

def ok := 1

/-- info: [true, true, true] -/
#guard_msgs in
run_meta do
  realizeConst ``ok `ok.l1 do
    realizeConst ``ok `ok.l2 do
      realizeConst ``ok `ok.l3 do
        addThm `ok.l3 (mkConst ``True) (mkConst ``True.intro)
      addThm `ok.l2 (mkConst ``True) (mkConst ``True.intro)
    addThm `ok.l1 (mkConst ``True) (mkConst ``True.intro)
  logInfo m!"{[← inKernelEnv `ok.l1, ← inKernelEnv `ok.l2, ← inKernelEnv `ok.l3]}"

/-! An ill-typed theorem created at depth 2 is rejected. -/

def bad2 := 1

/--
info: [false, false]
---
error: (kernel) declaration type mismatch, 'bad2.l2' has type
  True
but it is expected to have type
  False
-/
#guard_msgs in
run_meta do
  realizeConst ``bad2 `bad2.l1 do
    realizeConst ``bad2 `bad2.l2 do
      addThm `bad2.l2 (mkConst ``False) (mkConst ``True.intro)
    addThm `bad2.l1 (mkConst ``True) (mkConst ``True.intro)
  logInfo m!"{[← inKernelEnv `bad2.l1, ← inKernelEnv `bad2.l2]}"

/-! An ill-typed theorem created at depth 3 is rejected. -/

def bad3 := 1

/--
info: [false, false, false]
---
error: (kernel) declaration type mismatch, 'bad3.l3' has type
  True
but it is expected to have type
  False
-/
#guard_msgs in
run_meta do
  realizeConst ``bad3 `bad3.l1 do
    realizeConst ``bad3 `bad3.l2 do
      realizeConst ``bad3 `bad3.l3 do
        addThm `bad3.l3 (mkConst ``False) (mkConst ``True.intro)
      addThm `bad3.l2 (mkConst ``True) (mkConst ``True.intro)
    addThm `bad3.l1 (mkConst ``True) (mkConst ``True.intro)
  logInfo m!"{[← inKernelEnv `bad3.l1, ← inKernelEnv `bad3.l2, ← inKernelEnv `bad3.l3]}"
