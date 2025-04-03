import Lake
open Lake DSL

package precompileArgs

@[default_target]
lean_lib Foo where
  precompileModules := true
  platformIndependent := if get_config? platformIndependent |>.isSome then true else none
  moreLinkArgs := if let some cfg := get_config? linkArgs then cfg.splitOn " " |>.toArray else #[]

lean_lib FooDep
lean_lib FooDepDep
lean_exe orderTest
