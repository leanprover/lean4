import Lean
/-!
Constants created by a realization, including one nested in another realization, are type checked
by the kernel where they are declared and are copied from there into the kernel environments of the
requesters. In particular, an ill-typed constant is still rejected, the error is reported once, and
the constant becomes an axiom like any other declaration the kernel rejects.
-/
open Lean Meta

/-- Adds the theorem `name : type := value`. -/
def addThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| .thmDecl { name, levelParams := [], type, value }

/-- Returns the kind of `name` in the kernel environment. -/
def kernelKind (name : Name) : MetaM String :=
  return match (← getEnv).toKernelEnv.find? name with
    | some (.thmInfo _)   => "theorem"
    | some (.axiomInfo _) => "axiom"
    | some _              => "other"
    | none                => "missing"

/-! Well-typed theorems created at depths 1, 2 and 3 are added to the kernel environment. -/

def ok := 1

/-- info: [theorem, theorem, theorem] -/
#guard_msgs in
run_meta do
  realizeConst ``ok `ok.l1 do
    realizeConst ``ok `ok.l2 do
      realizeConst ``ok `ok.l3 do
        addThm `ok.l3 (mkConst ``True) (mkConst ``True.intro)
      addThm `ok.l2 (mkConst ``True) (mkConst ``True.intro)
    addThm `ok.l1 (mkConst ``True) (mkConst ``True.intro)
  logInfo m!"{[← kernelKind `ok.l1, ← kernelKind `ok.l2, ← kernelKind `ok.l3]}"

/-! An ill-typed theorem created at depth 2 is rejected. -/

def bad2 := 1

/--
info: [theorem, axiom]
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
  logInfo m!"{[← kernelKind `bad2.l1, ← kernelKind `bad2.l2]}"

/-! An ill-typed theorem created at depth 3 is rejected. -/

def bad3 := 1

/--
info: [theorem, theorem, axiom]
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
  logInfo m!"{[← kernelKind `bad3.l1, ← kernelKind `bad3.l2, ← kernelKind `bad3.l3]}"
