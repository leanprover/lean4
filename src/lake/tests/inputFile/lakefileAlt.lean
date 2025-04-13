import Lake

open System Lake DSL

package test

input_file foo where
  path := "inputs/foo.txt"
  text := true

input_dir barz where
  path := "inputs/barz"
  text := true
  filter := .fileName (.startsWith "b")

@[default_target]
lean_exe test where
  needs := #[foo, barz]
