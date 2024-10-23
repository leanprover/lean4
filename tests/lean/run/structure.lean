import Lean

open Lean

structure S1 :=
(x y : Nat)

structure S2 extends S1 :=
(z : Nat)

structure S3 :=
(w : Nat)

structure S4 extends S2, S3 :=
(s : Nat)

def check (b : Bool) : CoreM Unit :=
unless b do throwError "check failed"

class S5 :=
(x y : Nat)

inductive D
| mk (x y z : Nat) : D

def tst : CoreM Unit :=
do let env ← getEnv
   IO.println (getStructureFields env `Lean.Environment)
   check $ getStructureFields env `S4 == #[`toS2, `toS3, `s]
   check $ getStructureFields env `S1 == #[`x, `y]
   check $ isSubobjectField? env `S4 `toS2 == some `S2
   check $ getParentStructures env `S4 == #[`S2, `S3]
   check $ findField? env `S4 `x == some `S1
   check $ findField? env `S4 `x1 == none
   check $ isStructure env `S1
   check $ isStructure env `S2
   check $ isStructure env `S3
   check $ isStructure env `S4
   check $ isStructure env `S5
   check $ !isStructure env `Nat
   check $ !isStructure env `D
   IO.println (getStructureFieldsFlattened env `S4)
   IO.println (getPathToBaseStructure? env `S1 `S4)
   IO.println (getParentStructures env `S4)
   IO.println (getAllParentStructures env `S4)
   check $ getPathToBaseStructure? env `S1 `S4 == some [`S4.toS2, `S2.toS1]
   pure ()

/--
info: #[const2ModIdx, constants, extensions, extraConstNames, header]
#[toS2, toS1, x, y, z, toS3, w, s]
(some [S4.toS2, S2.toS1])
#[S2, S3]
#[S2, S1, S3]
-/
#guard_msgs in
#eval tst

/-!
Regression test: make sure mathlib `Type*` still elaborates with levels in correct order.
-/
section
elab "Type*" : term => do
  let u ← Lean.Meta.mkFreshLevelMVar
  Lean.Elab.Term.levelMVarToParam (.sort (.succ u))

variable {F α β M N P G H : Type*}

structure AddEquiv (A B : Type*) : Type

/-- info: AddEquiv.{u_9, u_10} (A : Type u_9) (B : Type u_10) : Type -/
#guard_msgs in #check AddEquiv
end
