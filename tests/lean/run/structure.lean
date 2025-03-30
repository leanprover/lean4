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

/--
info: #[constants, quotInit, diagnostics, const2ModIdx, extensions, extraConstNames, header]
#[toS2, toS1, x, y, z, toS3, w, s]
(some [S4.toS2, S2.toS1])
#[S2, S3]
#[S2, S3, S1]
-/
#guard_msgs in
#eval show CoreM Unit from do
  let env ← getEnv
  IO.println (getStructureFields env ``Kernel.Environment)
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
  check $ getPathToBaseStructure? env `S1 `S4 == some [`S4.toS2, `S2.toS1]
  IO.println (getStructureFieldsFlattened env `S4)
  IO.println (getPathToBaseStructure? env `S1 `S4)
  IO.println (getStructureSubobjects env `S4)
  IO.println (← getAllParentStructures `S4)
  pure ()

def dumpStructInfo (structName : Name) : CoreM Unit := do
  let env ← getEnv
  let some info := getStructureInfo? env structName
    | throwError "no such structure {structName}"
  IO.println s!"\
    struct: {info.structName}\n\
    fields: {info.fieldNames}\n\
    field infos: {info.fieldInfo.map fun info => s!"({info.fieldName}, {info.subobject?}, {info.projFn})"}\n\
    parent infos: {info.parentInfo.map fun info => (info.structName, info.subobject, info.projFn)}"

/--
info: struct: S1
fields: #[x, y]
field infos: #[(y, none, S1.y), (x, none, S1.x)]
parent infos: #[]
-/
#guard_msgs in #eval dumpStructInfo `S1
/--
info: struct: S2
fields: #[toS1, z]
field infos: #[(z, none, S2.z), (toS1, (some S1), S2.toS1)]
parent infos: #[(S1, (true, S2.toS1))]
-/
#guard_msgs in #eval dumpStructInfo `S2
/--
info: struct: S3
fields: #[w]
field infos: #[(w, none, S3.w)]
parent infos: #[]
-/
#guard_msgs in #eval dumpStructInfo `S3
/--
info: struct: S4
fields: #[toS2, toS3, s]
field infos: #[(s, none, S4.s), (toS2, (some S2), S4.toS2), (toS3, (some S3), S4.toS3)]
parent infos: #[(S2, (true, S4.toS2)), (S3, (true, S4.toS3))]
-/
#guard_msgs in #eval dumpStructInfo `S4


/-!
Basic diamond
-/

structure A1 where
  x : Nat
structure A2 extends A1 where
  y : Nat
structure A3 extends A1 where
  z : Nat
structure A4 extends A2, A3 where
  w : Nat

/--
info: struct: A1
fields: #[x]
field infos: #[(x, none, A1.x)]
parent infos: #[]
-/
#guard_msgs in #eval dumpStructInfo `A1
/--
info: struct: A2
fields: #[toA1, y]
field infos: #[(y, none, A2.y), (toA1, (some A1), A2.toA1)]
parent infos: #[(A1, (true, A2.toA1))]
-/
#guard_msgs in #eval dumpStructInfo `A2
/--
info: struct: A3
fields: #[toA1, z]
field infos: #[(z, none, A3.z), (toA1, (some A1), A3.toA1)]
parent infos: #[(A1, (true, A3.toA1))]
-/
#guard_msgs in #eval dumpStructInfo `A3
/--
info: struct: A4
fields: #[toA2, z, w]
field infos: #[(z, none, A4.z), (w, none, A4.w), (toA2, (some A2), A4.toA2)]
parent infos: #[(A2, (true, A4.toA2)), (A3, (false, A4.toA3))]
-/
#guard_msgs in #eval dumpStructInfo `A4

/-!
Abbreviation in parent
-/
abbrev AA1 := A1
structure A5 extends AA1 where
  a : Nat
/--
info: struct: A5
fields: #[toA1, a]
field infos: #[(a, none, A5.a), (toA1, (some A1), A5.toA1)]
parent infos: #[(A1, (true, A5.toA1))]
-/
#guard_msgs in #eval dumpStructInfo `A5


/-!
Regression test: make sure mathlib `Type*` still elaborates with levels in correct order.
During development, this came out as `AddEquiv.{u_10, u_9}`.
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
