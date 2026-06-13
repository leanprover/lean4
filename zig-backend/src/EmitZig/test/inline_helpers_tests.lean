module

import EmitZig.CLI

/-! Tests inline helper emission for M6-C7. -/

open System

namespace inline_helpers_tests

private def mkTempDir : IO FilePath := do
  IO.FS.createTempDir

private unsafe def emitSource (fileName source : String) : IO (FilePath × String) := do
  let dir ← mkTempDir
  let input := dir / fileName
  let output := dir / "out.zig"
  IO.FS.writeFile input source
  let rc ← EmitZig.emitzigMain [input.toString, "-o", output.toString]
  assert! rc == 0
  return (output, ← IO.FS.readFile output)

private def assertBuildObj (zigFile : FilePath) : IO Unit := do
  let out ← IO.Process.output {
    cmd := "zig"
    args := #["build-obj", "-O", "Debug", "--name", "probe", "-femit-bin=/dev/null", zigFile.toString]
  }
  assert! out.exitCode == 0

private def assertInlineNotExtern (text helper : String) : IO Unit := do
  assert! text.contains s!"inline fn {helper}("
  assert! !text.contains s!"extern fn {helper}("

private def assertExternNotInline (text helper : String) : IO Unit := do
  assert! text.contains s!"extern fn {helper}("
  assert! !text.contains s!"inline fn {helper}("

public unsafe def runTests : IO Unit := do
  let (coreFile, coreText) ← emitSource "CoreHelpers.lean" <| String.intercalate "\n" [
    "module",
    "",
    "def tupleHead (p : Nat × Nat) : Nat :=",
    "  p.1",
    "",
    "def main : IO UInt32 := do",
    "  let pair : Nat × Nat := (41, 42)",
    "  let total : Nat := tupleHead pair + 7",
    "  let code : UInt32 := if total == 90 then 7 else 9",
    "  pure code"
  ]
  for helper in [
    "lean_unsigned_to_nat",
    "lean_box",
    "lean_unbox_uint32",
    "lean_io_result_mk_ok",
    "lean_obj_tag",
    "lean_ctor_get",
    "lean_ctor_set_tag",
    "lean_inc",
    "lean_dec",
    "lean_dec_ref",
    "lean_inc_ref",
    "lean_alloc_ctor"
  ] do
    assertInlineNotExtern coreText helper
  assertBuildObj coreFile

  let (ioFile, ioText) ← emitSource "IoWorldHelper.lean" <| String.intercalate "\n" [
    "module",
    "",
    "@[extern \"lean_io_mk_world\"]",
    "opaque ioWorld : Unit",
    "",
    "def world : Unit :=",
    "  ioWorld"
  ]
  assertInlineNotExtern ioText "lean_io_mk_world"
  assert! ioText.contains "lean_io_mk_world()"
  assertBuildObj ioFile

  let (arrayFile, arrayText) ← emitSource "ArrayLoopHelpers.lean" <| String.intercalate "\n" [
    "module",
    "",
    "def main : IO Unit := do",
    "  let xs : Array UInt32 := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]",
    "  let total : UInt32 := xs.foldl (fun acc x => acc + x) 0",
    "  IO.println (toString total)"
  ]
  for helper in [
    "lean_array_get_size",
    "lean_array_uget_borrowed",
    "lean_mk_empty_array_with_capacity",
    "lean_nat_dec_le",
    "lean_nat_dec_lt",
    "lean_uint32_add",
    "lean_uint32_to_nat",
    "lean_usize_add",
    "lean_usize_dec_eq",
    "lean_usize_of_nat"
  ] do
    assertInlineNotExtern arrayText helper
  assertBuildObj arrayFile

  let (bignumFile, bignumText) ← emitSource "BigNatHelpers.lean" <| String.intercalate "\n" [
    "module",
    "",
    "def work (x y : Nat) : Nat × Nat × Nat × Nat × Nat × Bool × Bool × Bool × UInt32 × UInt64 :=",
    "  let add := x + y",
    "  let sub := add - x",
    "  let mul := sub * y",
    "  let div := mul / (x + 1)",
    "  let mod := mul % (y + 1)",
    "  let eq : Bool := add == sub",
    "  let le : Bool := div ≤ mul",
    "  let lt : Bool := mod < mul",
    "  let pow := Nat.pow div 3",
    "  (add, sub, mul, div, mod, eq, le, lt, UInt32.ofNat pow, UInt64.ofNat pow)",
    "",
    "def big1 : Nat := 4294967296 * 4294967296 + 123",
    "def big2 : Nat := 18446744073709551616 + 456",
    "",
    "def main : IO Unit := do",
    "  let (add, sub, mul, div, mod, eq, le, lt, u32, u64) := work big1 big2",
    "  IO.println s!\"{add} {sub} {mul} {div} {mod} {eq} {le} {lt} {u32.toNat} {u64.toNat}\""
  ]
  for helper in [
    "lean_uint64_to_nat",
    "lean_nat_add",
    "lean_nat_sub",
    "lean_nat_mul",
    "lean_nat_div",
    "lean_nat_mod",
    "lean_nat_eq",
    "lean_nat_dec_eq",
    "lean_nat_dec_le",
    "lean_nat_dec_lt",
    "lean_uint32_of_nat",
    "lean_uint64_of_nat"
  ] do
    assertInlineNotExtern bignumText helper
  for helper in [
    "lean_nat_big_succ",
    "lean_nat_big_add",
    "lean_nat_big_sub",
    "lean_nat_overflow_mul",
    "lean_nat_big_mul",
    "lean_nat_big_div",
    "lean_nat_big_mod",
    "lean_nat_big_eq",
    "lean_nat_big_le",
    "lean_nat_big_lt",
    "lean_nat_pow",
    "lean_cstr_to_nat",
    "lean_big_uint64_to_nat",
    "lean_uint32_of_big_nat",
    "lean_uint64_of_big_nat"
  ] do
    assertExternNotInline bignumText helper
  for snippet in [
    " = lean_nat_add(",
    " = lean_nat_sub(",
    " = lean_nat_mul(",
    " = lean_nat_div(",
    " = lean_nat_mod(",
    " = lean_nat_dec_eq(",
    " = lean_nat_dec_le(",
    " = lean_nat_dec_lt(",
    " = lean_nat_pow(",
    " = lean_uint32_of_nat(",
    " = lean_uint64_of_nat(",
    " = lean_uint64_to_nat("
  ] do
    assert! bignumText.contains snippet
  assertBuildObj bignumFile

end inline_helpers_tests
