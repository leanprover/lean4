module

import EmitZig.CLI

/-! Tests `emitLetDecl` function-application emission for M6-C2. -/

open System

namespace fap_pap_tests

private def mkTempDir : IO FilePath := do
  IO.FS.createTempDir

private unsafe def runEmit (fileName source : String) : IO String := do
  let dir ← mkTempDir
  let input := dir / fileName
  let output := dir / "out.zig"
  IO.FS.writeFile input source
  let rc ← EmitZig.emitzigMain [input.toString, "-o", output.toString]
  assert! rc == 0
  IO.FS.readFile output

private def assertContainsAll (text : String) (needles : List String) : IO Unit := do
  for needle in needles do
    assert! text.contains needle

private def checkZigCompiles (zigText : String) : IO Unit := do
  let dir ← mkTempDir
  let zigFile := dir / "out.zig"
  IO.FS.writeFile zigFile zigText
  let out ← IO.Process.output {
    cmd := "zig"
    args := #["build-obj", "-femit-bin=/dev/null", zigFile.toString]
  }
  assert! out.exitCode == 0

public unsafe def runTests : IO Unit := do
  let output ← runEmit "FapPap.lean" <| String.intercalate "\n" [
    "def strLen (s : String) : Nat := s.length",
    "def addNat (a b : Nat) : Nat := Nat.add a b",
    "def addOne : Nat → Nat := (· + 1)",
    "def fs : List (Nat → Nat) := [Nat.add 1]",
    "def big (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 : Nat) : Nat :=",
    "  a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15 + a16 + a17",
    "def useBig (x : Nat) : Nat :=",
    "  big x (x+1) (x+2) (x+3) (x+4) (x+5) (x+6) (x+7) (x+8) (x+9) (x+10) (x+11) (x+12) (x+13) (x+14) (x+15) (x+16)"
  ]
  assertContainsAll output [
    "extern fn lean_apply_n(",
    "extern fn lean_apply_1(",
    "extern fn lean_string_length(",
    "inline fn lean_nat_add(",
    " = lean_string_length(",
    " = lean_nat_add(",
    "lean_alloc_closure(@ptrCast(&l_Nat_add___boxed), @as(c_uint, 2), @as(c_uint, 1));",
    "lean_closure_set(",
    "lean_alloc_closure(@ptrCast(&l_big), @as(c_uint, 17), @as(c_uint, 0));",
    " = lean_apply_n("
  ]
  checkZigCompiles output

  let freeVarOut ← runEmit "FVarApp.lean" <| String.intercalate "\n" [
    "def applyTwice (f : Nat → Nat) (x : Nat) : Nat :=",
    "  f (f x)"
  ]
  assertContainsAll freeVarOut [
    " = lean_apply_1(",
    "fn l_applyTwice__def"
  ]
  assert! !freeVarOut.contains "EmitZig body emission not implemented yet"
  checkZigCompiles freeVarOut

end fap_pap_tests
