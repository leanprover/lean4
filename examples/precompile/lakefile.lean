import Lake
open Lake DSL

package precompile {
  precompileModules := true
}

@[defaultTarget]
lean_lib Precompile
