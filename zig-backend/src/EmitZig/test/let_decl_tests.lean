module

import EmitZig
import EmitZig.CLI
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.Types

/-! Tests core `emitLetDecl` value-case emission for M6-C1. -/

open System Lean

namespace let_decl_tests

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

private def mkFVar (name : Name) : FVarId :=
  Lean.FVarId.mk name

private def renderCore (binder : Name) (type : Expr)
    (value : Lean.Compiler.LCNF.LetValue .impure) : String :=
  match EmitZig.renderCoreLetValueLines? binder type value with
  | some lines => String.intercalate "\n" lines
  | none => panic! "expected supported core let value"

private def checkZigCompiles (zigFile : FilePath) : IO Unit := do
  let out ← IO.Process.output {
    cmd := "zig"
    args := #["build-obj", "-femit-bin=/dev/null", zigFile.toString]
  }
  assert! out.exitCode == 0

public unsafe def runTests : IO Unit := do
  let ctorOut := renderCore `pair Lean.Compiler.LCNF.ImpureType.object <|
    .ctor { name := `Prod.mk, cidx := 0, size := 2, usize := 0, ssize := 0 }
      #[.fvar (mkFVar `lhs), .fvar (mkFVar `rhs)]
  assertContainsAll ctorOut [
    "v_pair = lean_alloc_ctor(@as(c_uint, 0), @as(c_uint, 2), @as(usize, 0));",
    "lean_ctor_set(v_pair, @as(c_uint, 0), v_lhs);",
    "lean_ctor_set(v_pair, @as(c_uint, 1), v_rhs);"
  ]

  let projOut := String.intercalate "\n" [
    renderCore `obj Lean.Compiler.LCNF.ImpureType.object (.oproj 1 (mkFVar `pair)),
    renderCore `u Lean.Compiler.LCNF.ImpureType.usize (.uproj 0 (mkFVar `pair)),
    renderCore `n Lean.Compiler.LCNF.ImpureType.uint32 (.sproj 1 4 (mkFVar `pair))
  ]
  assertContainsAll projOut [
    "v_obj = lean_ctor_get(v_pair, @as(c_uint, 1));",
    "v_u = lean_ctor_get_usize(v_pair, @as(c_uint, 0));",
    "v_n = lean_ctor_get_uint32(v_pair, @as(c_uint, @sizeOf(usize) * 1 + 4));"
  ]

  let boxOut := String.intercalate "\n" [
    renderCore `boxed8 Lean.Compiler.LCNF.ImpureType.tobject
      (.box Lean.Compiler.LCNF.ImpureType.uint8 (mkFVar `src8)),
    renderCore `boxed32 Lean.Compiler.LCNF.ImpureType.tobject
      (.box Lean.Compiler.LCNF.ImpureType.uint32 (mkFVar `src32)),
    renderCore `unboxed8 Lean.Compiler.LCNF.ImpureType.uint8 (.unbox (mkFVar `boxedVal)),
    renderCore `shared Lean.Compiler.LCNF.ImpureType.uint8 (.isShared (mkFVar `obj))
  ]
  assertContainsAll boxOut [
    "v_boxed8 = lean_box(@as(usize, @intCast(v_src8)));",
    "v_boxed32 = lean_box_uint32(v_src32);",
    "v_unboxed8 = @as(u8, @truncate(lean_unbox(v_boxedVal)));",
    "v_shared = @as(u8, @intFromBool(!lean_is_exclusive(v_obj)));"
  ]

  let litOut := String.intercalate "\n" [
    renderCore `u32v Lean.Compiler.LCNF.ImpureType.uint32 (.lit (.uint32 42)),
    renderCore `smallNat Lean.Compiler.LCNF.ImpureType.object (.lit (.nat 42)),
    renderCore `bigNat Lean.Compiler.LCNF.ImpureType.object (.lit (.nat (UInt32.size + 1))),
    renderCore `strv Lean.Compiler.LCNF.ImpureType.object (.lit (.str "hello")),
    renderCore `erasedv Lean.Compiler.LCNF.ImpureType.object .erased
  ]
  assertContainsAll litOut [
    "v_u32v = @as(u32, 42);",
    "v_smallNat = lean_unsigned_to_nat(@as(c_uint, 42));",
    "v_bigNat = lean_cstr_to_nat(\"4294967297\");",
    "v_strv = lean_mk_string_unchecked(\"hello\", @as(usize, 5), @as(usize, 5));",
    "v_erasedv = lean_box(@as(usize, 0));"
  ]

  let dir ← mkTempDir
  let input := dir / "PairSmoke.lean"
  let output := dir / "PairSmoke.zig"
  IO.FS.writeFile input <|
    String.intercalate "\n" [
      "def mkPair (x y : Nat) : Nat × Nat := (x, y)",
      "def fstProj (p : Nat × Nat) : Nat := p.1",
      "def sndProj (p : Nat × Nat) : Nat := p.2"
    ]
  let rc ← EmitZig.emitzigMain [input.toString, "-o", output.toString]
  assert! rc == 0
  let smokeOut ← IO.FS.readFile output
  assertContainsAll smokeOut [
    "lean_alloc_ctor(@as(c_uint, 0), @as(c_uint, 2), @as(usize, 0));",
    "lean_ctor_get(v___uniq_1_, @as(c_uint, 0));",
    "lean_ctor_get(v___uniq_1_, @as(c_uint, 1));"
  ]
  checkZigCompiles output
