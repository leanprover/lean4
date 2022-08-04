import Lake
open System Lake DSL

package ffi {
  srcDir := "lean"
  precompileModules := true
}

lean_lib FFI

@[defaultTarget] lean_exe test {
  root := `Main
}

target ffi.o : FilePath := fun pkg _ => do
  let oFile := pkg.buildDir / "c" / "ffi.o"
  let srcJob ← inputFile <| pkg.dir / "c" / "ffi.cpp"
  buildFileAfterDep oFile srcJob fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
    compileO "ffi.c" oFile srcFile flags "c++"

extern_lib libleanffi := fun pkg _ => do
  let name := nameToStaticLib "leanffi"
  let ffiO ← recBuild <| pkg.customTarget ``ffi.o
  buildStaticLib (pkg.buildDir / "c" / name) #[ffiO]
