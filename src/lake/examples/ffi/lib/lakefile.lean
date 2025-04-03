import Lake
open System Lake DSL

package ffi where
  srcDir := "lean"

@[default_target]
lean_exe test where
  root := `Main

lean_lib FFI

/-! ## Static C FFI Library -/

input_file ffi_static.c where
  path := "c" / "ffi_static.c"
  text := true

target ffi_static.o pkg : FilePath := do
  let srcJob ← ffi_static.c.fetch
  let oFile := pkg.buildDir / "c" / "ffi_static.o"
  buildO oFile srcJob #[] #["-fPIC"] "cc"

target libleanffi_static pkg : FilePath := do
  let ffiO ← ffi_static.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_lib FFI.Static where
  moreLinkObjs := #[libleanffi_static]

/-! ## Shared C++ FFI Library -/

input_file ffi_shared.cpp where
  path := "c" / "ffi_shared.cpp"
  text := true

target ffi_shared.o pkg : FilePath := do
  let srcJob ← ffi_shared.cpp.fetch
  let oFile := pkg.buildDir / "c" / "ffi_shared.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "c++" getLeanTrace

target libleanffi_shared pkg : Dynlib := do
  let libName := "leanffi"
  let ffiO ← ffi_shared.o.fetch
  let leanArgs ← getLeanLinkSharedFlags
  buildSharedLib libName (pkg.sharedLibDir / nameToSharedLib libName)
    #[ffiO] #[] #[] leanArgs "c++" getLeanTrace

lean_lib FFI.Shared where
  moreLinkLibs := #[libleanffi_shared]
