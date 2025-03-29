import Lake
open System Lake DSL

package ffi where
  srcDir := "lean"

@[default_target]
lean_exe test where
  root := `Main

input_file ffi.cpp where
  path := "c" / "ffi.cpp"
  text := true

target ffi.o pkg : FilePath := do
  let srcJob ← ffi.cpp.fetch
  let oFile := pkg.buildDir / "c" / "ffi.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "c++" getLeanTrace

target libleanffi pkg : FilePath := do
  let ffiO ← ffi.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]

lean_lib FFI where
  moreLinkObjs := #[libleanffi]
