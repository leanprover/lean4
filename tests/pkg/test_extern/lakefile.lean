import Lake
open System Lake DSL

package test_extern where
  precompileModules := true
  moreLinkArgs := #["-v", "-L/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib"]

@[default_target] lean_lib TestExtern
