module

/-! A borrow annotation on a scalar parameter of an `[extern]` declaration is dropped in the IR. -/

set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in

@[extern "lean_string_of_usize"]
def usizeReprBorrowed (n : @& USize) : String :=
  ""
