import Lake
open Lake DSL

package precompileArgs

@[default_target]
lean_lib Foo {
  precompileModules := true
  moreLinkArgs := #["-lBaz"]
}

