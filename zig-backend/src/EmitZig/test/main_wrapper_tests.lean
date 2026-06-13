module

import EmitZig.CLI

/-! Tests full `main` wrapper emission for M6-C5. -/

open System

namespace main_wrapper_tests

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

public unsafe def runTests : IO Unit := do
  let ioOut ← runEmit "Hello.lean" "def main : IO Unit := IO.println \"Hi\"\n"
  assertContainsAll ioOut [
    "extern fn lean_setup_args(argc: c_int, argv: [*c][*c]u8) callconv(.c) [*c][*c]u8;",
    "extern fn lean_init_task_manager() callconv(.c) void;",
    "extern fn lean_finalize_task_manager() callconv(.c) void;",
    "fn lean_io_result_is_ok(r: LeanObj) bool {",
    "fn lean_io_result_get_value(r: LeanObj) LeanObj {",
    "extern fn lean_io_result_show_error(r: LeanObj) callconv(.c) void;",
    "pub fn main(argc: c_int, argv0: [*c][*c]u8) callconv(.c) c_int {",
    "lean_setup_args(argc, argv0);",
    "lean_initialize_runtime_module();",
    "lean_io_mark_end_initialization();",
    "lean_init_task_manager();",
    "lean_run_main(emitzig_run_main, argc, argv);",
    "lean_finalize_task_manager();",
    "lean_io_result_show_error(res);"
  ]

  let argvOut ← runEmit "ArgsMain.lean" <| String.intercalate "\n" [
    "def main (args : List String) : IO UInt32 :=",
    "  pure 7"
  ]
  assertContainsAll argvOut [
    "var in = lean_box(@as(usize, 0));",
    "while (i > 1) {",
    "lean_alloc_ctor(@as(c_uint, 1), @as(c_uint, 2), @as(usize, 0));",
    "lean_mk_string(argv[i])",
    "return _lean_main(in);",
    "lean_unbox_uint32(lean_io_result_get_value(res))"
  ]

end main_wrapper_tests
