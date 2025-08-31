import Lake

open Lake DSL System

package ffi

input_file a.c where
  path := "a.c"
  text := true

target a.o pkg : FilePath := do
  let srcJob ← a.c.fetch
  let oFile := pkg.buildDir / "a" / "a.o"
  let flags := #["-fPIC"]
  buildO oFile srcJob flags

@[default_target]
lean_lib A where
  precompileModules := true
  moreLinkObjs := #[a.o]

@[default_target]
lean_lib B where
  --precompileModules := true
