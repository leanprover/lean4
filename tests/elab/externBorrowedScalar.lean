module

/-! A borrow annotation on a scalar parameter of an `[extern]` declaration is dropped in the IR. -/

set_option trace.compiler.ir.result true

@[extern "lean_string_of_usize"]
def usizeReprBorrowed (n : @& USize) : String :=
  ""
