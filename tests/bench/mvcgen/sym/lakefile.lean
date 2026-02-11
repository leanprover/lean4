import Lake
open System Lake DSL

package mvcgen_bench where
  precompileModules := true

lean_lib VCGen where
  srcDir := "lib"

lean_lib Baseline where
  srcDir := "lib"

@[default_target]
lean_lib VCGenBench where
  roots := #[`vcgen_add_sub_cancel, `vcgen_deep_add_sub_cancel, `vcgen_get_throw_set]
  moreLeanArgs := #["--tstack=100000000"]

@[default_target]
lean_lib BaselineBench where
  roots := #[`baseline_add_sub_cancel]
  moreLeanArgs := #["--tstack=100000000"]
