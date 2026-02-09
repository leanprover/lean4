module

/-! Applying `[extern]` to a projection should insert necessary `dec`s in `_boxed`. -/

structure Foo where
  bar : UInt64 → UInt64

set_option trace.compiler.ir.result true
attribute [extern "does_not_exist"] Foo.bar
