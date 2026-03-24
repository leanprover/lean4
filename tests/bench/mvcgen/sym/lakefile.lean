import Lake
open System Lake DSL

package mvcgen_bench where
  precompileModules := true

lean_lib VCGen where
  srcDir := "lib"

lean_lib Baseline where
  srcDir := "lib"

lean_lib Driver where
  srcDir := "lib"

lean_lib Cases where
  srcDir := "cases"

@[default_target]
lean_lib VCGenBench where
  roots := #[`vcgen_add_sub_cancel, `vcgen_add_sub_cancel_deep, `vcgen_add_sub_cancel_simp,
             `vcgen_get_throw_set, `vcgen_pure_precond, `vcgen_reader_state]
  moreLeanArgs := #["--tstack=100000000"]

@[default_target]
lean_lib BaselineBench where
  roots := #[`baseline_add_sub_cancel]
  moreLeanArgs := #["--tstack=100000000"]

@[test_driver]
lean_lib VCGenTest where
  roots := #[`test_vcgen]
