module

import test.file_level_tests
import test.main_wrapper_tests
import test.fap_pap_tests
import test.let_decl_tests
import test.control_flow_tests
import test.reset_reuse_sset_tests
import test.runnable_tests
import test.inline_helpers_tests

public unsafe def main : IO UInt32 := do
  file_level_tests.runTests
  main_wrapper_tests.runTests
  fap_pap_tests.runTests
  let_decl_tests.runTests
  control_flow_tests.runTests
  reset_reuse_sset_tests.runTests
  runnable_tests.runTests
  inline_helpers_tests.runTests
  IO.println "EmitZig file-level, main-wrapper, let-decl, fap/pap, control-flow, reset/reuse/sset, runnable, and inline-helper tests passed"
  return 0
