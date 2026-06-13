module

import EmitZig.CLI

/-! Runnable regression tests for M6-C6 end-to-end emitter correctness. -/

open System

namespace runnable_tests

private def getGmpPrefix : IO FilePath := do
  return (← IO.getEnv "GMP_PREFIX").getD "/opt/homebrew/opt/gmp"

private def getLibuvPrefix : IO FilePath := do
  return (← IO.getEnv "LIBUV_PREFIX").getD "/opt/homebrew/opt/libuv"

private def mkTempDir : IO FilePath := do
  IO.FS.createTempDir

private def runChecked (cmd : String) (args : Array String) (cwd : FilePath := ".") : IO IO.Process.Output := do
  let out ← IO.Process.output { cmd, args, cwd }
  unless out.exitCode == 0 do
    panic! s!"command failed: {cmd} {String.intercalate " " args.toList}\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}"
  pure out

private unsafe def emitSource (fileName source : String) : IO (FilePath × String) := do
  let dir ← mkTempDir
  let input := dir / fileName
  let output := dir / s!"{input.fileStem.getD "out"}.zig"
  IO.FS.writeFile input source
  let rc ← EmitZig.emitzigMain [input.toString, "-o", output.toString]
  assert! rc == 0
  return (output, ← IO.FS.readFile output)

private def assertBuildObj (zigFile : FilePath) : IO Unit := do
  let _ ← runChecked "zig" #[
    "build-obj", zigFile.toString, "-O", "Debug",
    "--name", "probe", "-femit-bin=/dev/null"
  ]
  pure ()

private def assertContainsAll (text : String) (needles : List String) : IO Unit := do
  for needle in needles do
    assert! text.contains needle

private unsafe def checkHelloRuns (zigFile : FilePath) : IO Unit := do
  let lean4Dir ← EmitZig.lean4Dir
  let zigBackendDir ← EmitZig.zigBackendDir
  let smokeCommonDir := zigBackendDir / "tests" / "emitzig-smoke" / "common"
  let stage1IncludeDir := lean4Dir / "build" / "release" / "stage1" / "include"
  let leanIncludeDir := lean4Dir / "src" / "include"
  let gmpPrefix ← getGmpPrefix
  let libuvPrefix ← getLibuvPrefix
  let dir := zigFile.parent.getD "."
  let includeDir := dir / "include"
  let driverO := dir / "driver.o"
  let compatO := dir / "compat.o"
  let emitzigO := dir / "hello.o"
  let bin := dir / "hello"

  let _ ← runChecked "bash"
    #[ (smokeCommonDir / "write_config_stub.sh").toString, includeDir.toString ]
  let _ ← runChecked "cc" #[
    "-Wall", "-Wextra", "-pedantic", "-x", "c", "-std=c11", "-c",
    "-DEMITZIG_INIT_FN=initialize_Hello",
    "-DEMITZIG_MAIN_FN=l___private_Hello_0__main",
    "-I", includeDir.toString,
    "-I", leanIncludeDir.toString,
    "-I", stage1IncludeDir.toString,
    (smokeCommonDir / "driver.c").toString,
    "-o", driverO.toString
  ]
  let _ ← runChecked "c++" #[
    "-Wall", "-Wextra", "-pedantic", "-std=c++17", "-c",
    "-I", includeDir.toString,
    "-I", leanIncludeDir.toString,
    "-I", stage1IncludeDir.toString,
    "-I", (lean4Dir / "src").toString,
    (smokeCommonDir / "compat.cpp").toString,
    "-o", compatO.toString
  ]
  let _ ← runChecked "zig"
    #["build-obj", zigFile.toString, "-O", "Debug", "--name", "probe", s!"-femit-bin={emitzigO}"]
  let _ ← runChecked "cc" #[
    emitzigO.toString,
    driverO.toString,
    compatO.toString,
    (zigBackendDir / "zig-out" / "lib" / "libleanrt-zig.a").toString,
    (zigBackendDir / "zig-out" / "lib" / "libleanrt_cpp_partial.a").toString,
    "-L", (lean4Dir / "build" / "release" / "stage1" / "lib" / "lean").toString,
    "-lleancpp", "-lInit", "-lStd", "-lLean", "-lLake",
    "-L", (gmpPrefix / "lib").toString, "-lgmp",
    "-L", (libuvPrefix / "lib").toString, "-luv",
    "-lc++", "-lpthread", "-lm",
    "-o", bin.toString
  ]
  let out ← runChecked bin.toString #[]
  assert! out.stdout == "Hello from EmitZig!\n"

public unsafe def runTests : IO Unit := do
  let (helloFile, helloText) ← emitSource "Hello.lean" <| String.intercalate "\n" [
    "module",
    "",
    "def main : IO Unit :=",
    "  IO.println \"Hello from EmitZig!\""
  ]
  assertContainsAll helloText [
    "fn initialize_Hello__def(builtin: u8) callconv(.c) LeanObj {",
    "var res: LeanObj = initialize_Hello__def(@as(u8, 1));"
  ]
  assert! !helloText.contains "runtime_initialize_Hello"
  assert! !helloText.contains "const _"
  assertBuildObj helloFile
  checkHelloRuns helloFile

  let (arithFile, arithText) ← emitSource "Arith.lean" <| String.intercalate "\n" [
    "module",
    "",
    "def main : IO Unit := do",
    "  let natPart : Nat := 17 + 25",
    "  let wordPart : UInt32 := 5 + 7",
    "  let total : Nat := natPart + wordPart.toNat",
    "  IO.println (toString total)"
  ]
  assert! !arithText.contains "runtime_initialize_Arith"
  assert! !arithText.contains "const _"
  assertBuildObj arithFile

  let (tailFile, tailText) ← emitSource "TailSum.lean" <| String.intercalate "\n" [
    "module",
    "",
    "def tailSum (limit acc n : Nat) : Nat :=",
    "  match n with",
    "  | 0 => acc + limit",
    "  | Nat.succ k => tailSum limit (acc + n) k"
  ]
  assertContainsAll tailText ["while (true) {", "const tail_v_", "var tail_v_"]
  assert! !tailText.contains "const _"
  assertBuildObj tailFile

end runnable_tests
