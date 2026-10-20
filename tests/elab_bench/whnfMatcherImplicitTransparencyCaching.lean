/-!
Regression test for #14323.
The realization of `ConfigType.eq_1` inside `Lake.Config.ConfigDecl` was inefficient.
The underlying issue uncovered by #13895 is that `whnfMatcher` used a custom "can unfold?"
predicate, which indirectly disabled the WHNF cache because functions cannot be used as cache keys,
when at reducible, instances or implicit transparency.

This benchmark measures a definitional equality check that triggers an expensive WHNF reduction
at implicit transparency that is *very* expensive if uncached.
-/

open Lean

abbrev T (kind : Name) : Type :=
  match kind with
  | `lean_lib   => Nat
  | `lean_exe   => Int
  | `extern_lib => Bool
  | `extern_libb => Bool
  | `extern_libbb => Bool
  | `extern_libbbb => Bool
  | `extern_libbbbb => Bool
  | `extern_libbbbbb => Bool
  | `input_file => Unit
  | _           => Empty

example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
example : T `input_file = Unit := by with_implicit apply_rfl
