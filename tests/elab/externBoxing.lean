module

/-! Applying `[extern]` to a projection should insert necessary `dec`s in `_boxed`. -/

@[override_runtime_type obj]
structure Foo where
  bar : UInt64 → UInt64

set_option trace.compiler.ir.result true
attribute [extern "does_not_exist"] Foo.bar
