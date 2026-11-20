import Lean
/-!
Constants created by a realization are added to the kernel environment of the requester without
type checking them again. This is not sound for a constant that depends on another constant of the
realization when the requester already has a different constant of that name, so such a constant is
type checked in the environment of the requester.
-/
open Lean Meta

def nat := mkConst ``Nat

/-- Adds the definition `name : Nat := val`. -/
def addNatDef (name : Name) (val : Nat) : MetaM Unit :=
  addDecl <| .defnDecl {
    name, levelParams := [], type := nat, value := mkRawNatLit val
    hints := .abbrev, safety := .safe, all := [name] }

/-- Adds the theorem `name : c = 0 := Eq.refl 0`, which is type correct iff `c` unfolds to `0`. -/
def addEqZeroThm (name c : Name) : MetaM Unit :=
  addDecl <| .thmDecl {
    name, levelParams := []
    type := mkApp3 (mkConst ``Eq [1]) nat (mkConst c) (mkRawNatLit 0)
    value := mkApp2 (mkConst ``Eq.refl [1]) nat (mkRawNatLit 0) }

/-- Returns the kind of `name` in the kernel environment. -/
def kernelKind (name : Name) : MetaM String :=
  return match (← getEnv).toKernelEnv.find? name with
    | some (.thmInfo _)   => "theorem"
    | some (.defnInfo _)  => "definition"
    | some _              => "other"
    | none                => "missing"

/-- Realizes `{c}.thm : {c}.aux = 0` together with `{c}.aux := 0`. -/
def realizeThm (c : Name) : MetaM Unit :=
  realizeConst c (c ++ `thm) do
    addNatDef (c ++ `aux) 0
    addEqZeroThm (c ++ `thm) (c ++ `aux)

/-! Without a clash, the theorem is added. -/

def ok := 1

/-- info: [definition, theorem] -/
#guard_msgs in
run_meta do
  realizeThm ``ok
  logInfo m!"{[← kernelKind `ok.aux, ← kernelKind `ok.thm]}"

/-! The requester has the same definition: the theorem is added. -/

def same := 1

run_meta addNatDef `same.aux 0

/-- info: [definition, theorem] -/
#guard_msgs in
run_meta do
  realizeThm ``same
  logInfo m!"{[← kernelKind `same.aux, ← kernelKind `same.thm]}"

/-!
The requester has a different definition, for which the theorem does not hold: it is not added.
-/

def clash := 1

run_meta addNatDef `clash.aux 1

/-- info: [definition, missing] -/
#guard_msgs in
run_meta do
  realizeThm ``clash
  logInfo m!"{[← kernelKind `clash.aux, ← kernelKind `clash.thm]}"
