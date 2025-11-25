import Lake
open System Lake DSL

package ffi

lean_lib FFI

lean_exe test where
  root := `Main

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "ffi.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

extern_lib libleanffi pkg := do
  let ffiO ← ffi.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]
