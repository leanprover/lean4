module

import EmitZig
import EmitZig.CLI
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.Types

/-! Tests reset/reuse and scalar-store emission for M6-C3. -/

open Lean

namespace reset_reuse_sset_tests

private def assertContainsAll (text : String) (needles : List String) : IO Unit := do
  for needle in needles do
    assert! text.contains needle

private def mkFVar (name : Name) : FVarId :=
  Lean.FVarId.mk name

private def renderLet (binder : Name) (type : Expr)
    (value : Lean.Compiler.LCNF.LetValue .impure) : String :=
  match EmitZig.renderCoreLetValueLines? binder type value with
  | some lines => String.intercalate "\n" lines
  | none => panic! "expected supported let value"

public unsafe def runTests : IO Unit := do
  let resetOut := renderLet `token Lean.Compiler.LCNF.ImpureType.object (.reset 2 (mkFVar `orig))
  assertContainsAll resetOut [
    "if (lean_is_exclusive(v_orig)) {",
    "  lean_ctor_release(v_orig, @as(c_uint, 0));",
    "  lean_ctor_release(v_orig, @as(c_uint, 1));",
    "  v_token = v_orig;",
    "} else {",
    "  lean_dec_ref(v_orig);",
    "  v_token = lean_box(@as(usize, 0));"
  ]

  let reuseOut := renderLet `result Lean.Compiler.LCNF.ImpureType.object <|
    .reuse (mkFVar `token)
      { name := `Pair.mk, cidx := 3, size := 2, usize := 0, ssize := 0 }
      true
      #[.fvar (mkFVar `lhs), .fvar (mkFVar `rhs)]
  assertContainsAll reuseOut [
    "if (lean_is_scalar(v_token)) {",
    "  v_result = lean_alloc_ctor(@as(c_uint, 3), @as(c_uint, 2), @as(usize, 0));",
    "} else {",
    "  v_result = v_token;",
    "  lean_ctor_set_tag(v_result, @as(u8, 3));",
    "lean_ctor_set(v_result, @as(c_uint, 0), v_lhs);",
    "lean_ctor_set(v_result, @as(c_uint, 1), v_rhs);"
  ]

  let ssetOut := EmitZig.renderSsetLine (mkFVar `ctor) 1 4 (mkFVar `scalar) Lean.Compiler.LCNF.ImpureType.uint32
  assertContainsAll ssetOut [
    "lean_ctor_set_uint32(v_ctor, @as(c_uint, @sizeOf(usize) * 1 + 4), v_scalar);"
  ]

end reset_reuse_sset_tests
