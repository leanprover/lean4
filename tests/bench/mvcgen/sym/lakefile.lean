import Lake
open System Lake DSL

package mvcgen_bench where
  precompileModules := true

-- VCGen library (lib/VCGen.lean), built first and used by benchmarks
lean_lib VCGen where
  srcDir := "lib"

-- Individual benchmark modules in the package root; each can `import VCGen`
@[default_target]
lean_lib MvcgenBench where
  roots := #[`add_sub_cancel]
  moreLeanArgs := #["--tstack=100000000"]
