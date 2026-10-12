module

/-! Applying `[extern]` to a projection should insert necessary `dec`s in `_boxed`. -/

structure Foo where
  bar : UInt64 → UInt64

set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
attribute [extern "does_not_exist"] Foo.bar
