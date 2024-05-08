import Lake
open Lake DSL

package precompileArgs

@[default_target]
lean_lib Foo where
  precompileModules := true
  moreLinkArgs := #["-lBaz"]
