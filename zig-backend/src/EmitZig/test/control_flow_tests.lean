module

import EmitZig.CLI

/-! Tests control-flow emission for M6-C4. -/

open System

namespace control_flow_tests

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

private def assertWhileBlockContainsVar (text : String) : IO Unit := do
  let afterLoop :=
    match text.splitOn "while (true) {" with
    | _ :: afterLoop :: _ => afterLoop
    | _ => panic! "missing tail-recursive loop"
  assert! afterLoop.contains "var "

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
  let optionOut ← runEmit "OptionIf.lean" <| String.intercalate "\n" [
    "def pick (x : Option Nat) : Nat :=",
    "  match x with",
    "  | none => 0",
    "  | some n => n"
  ]
  assertContainsAll optionOut [
    "if (lean_obj_tag(",
    "} else {"
  ]

  let natOut ← runEmit "NatCases.lean" <| String.intercalate "\n" [
    "def pred' (n : Nat) : Nat :=",
    "  match n with",
    "  | 0 => 0",
    "  | Nat.succ k => k"
  ]
  assertContainsAll natOut [
    "lean_nat_dec_eq(",
    "if (",
    "lean_nat_sub("
  ]

  let joinOut ← runEmit "JoinPoint.lean" <| String.intercalate "\n" [
    "def branchJoin (b : Bool) (x y : Nat) : Nat :=",
    "  let z := if b then x else y",
    "  z + 1"
  ]
  assertContainsAll joinOut [
    ": {",
    "break :jp_",
    "lean_nat_add("
  ]

  let factOut ← runEmit "TailRec.lean" <| String.intercalate "\n" [
    "def factAux (acc n : Nat) : Nat :=",
    "  match n with",
    "  | 0 => acc",
    "  | Nat.succ k => factAux (acc * n) k"
  ]
  assertContainsAll factOut [
    "while (true) {",
    "continue;"
  ]
  assertWhileBlockContainsVar factOut
  checkZigCompiles factOut

end control_flow_tests
