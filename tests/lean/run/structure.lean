import Lean

open Lean

structure S1 where
  (x y : Nat)

structure S2 extends S1 where
  (z : Nat)

structure S3 where
  (w : Nat)

structure S4 extends S2, S3 where
  (s : Nat)

def check (b : Bool) : CoreM Unit :=
  unless b do throwError "check failed"

class S5 where
  (x y : Nat)

inductive D
  | mk (x y z : Nat) : D

def tst : CoreM Unit := do
  let env ← getEnv
  IO.println (getStructureFields env `Lean.Environment)
  check $ getStructureFields env `S4 == #[`toS2, `toS3, `s]
  check $ getStructureFields env `S1 == #[`x, `y]
  check $ isSubobjectField? env `S4 `toS2 == some `S2
  check $ getStructureSubobjects env `S4 == #[`S2, `S3]
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
  IO.println (getStructureSubobjects env `S4)
  IO.println (getAllParentStructures env `S4)
  IO.println (getStructureParentInfo env `S4 |>.map (fun i => (i.structName, i.projFn)))
  check $ getPathToBaseStructure? env `S1 `S4 == some [`S4.toS2, `S2.toS1]
  pure ()

/--
info: #[const2ModIdx, constants, extensions, extraConstNames, header]
#[toS2, toS1, x, y, z, toS3, w, s]
(some [S4.toS2, S2.toS1])
#[S2, S3]
#[S2, S1, S3]
#[(S2, S4.toS2), (S3, S4.toS3)]
-/
#guard_msgs in
#eval tst


structure A1 where
  x : Nat
structure A2 where
  y : Nat
structure A3 extends A2 where
  x : Nat
  z : Nat
structure A4 extends A1, A2
structure A4' extends A2, A1
structure A5 extends A1, A3
structure A5' extends A3, A1
abbrev AA1 := A1
abbrev AA3 := A3
structure A5'' extends A1, AA3
structure A5''' extends AA1, A3

def parentInfos (structName : Name) : Elab.Command.CommandElabM (Array (Name × Name)) := do
   return getStructureParentInfo (← getEnv) structName |>.map (fun i : StructureParentInfo => (i.structName, i.projFn))

/-- info: #[(`A1, `A4.toA1), (`A2, `A4.toA2)] -/
#guard_msgs in #eval parentInfos `A4
/-- info: #[(`A2, `A4'.toA2), (`A1, `A4'.toA1)] -/
#guard_msgs in #eval parentInfos `A4'
/-- info: #[(`A1, `A5.toA1), (`A3, `A5.toA3)] -/
#guard_msgs in #eval parentInfos `A5
/-- info: #[(`A3, `A5'.toA3), (`A1, `A5'.toA1)] -/
#guard_msgs in #eval parentInfos `A5'
/-- info: #[(`A1, `A5''.toA1), (`A3, `A5''.toA3)] -/
#guard_msgs in #eval parentInfos `A5''
/-- info: #[(`A1, `A5'''.toA1), (`A3, `A5'''.toA3)] -/
#guard_msgs in #eval parentInfos `A5'''
