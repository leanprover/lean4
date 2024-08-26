import Lake
open Lake DSL

package "mergeSortBenchmark" where
  -- add package configuration options here

@[default_target]
lean_exe "mergeSort" where
  root := `Bench
