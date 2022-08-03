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

def pkgDir := __dir__
def cSrcDir := pkgDir / "c"
def cBuildDir := pkgDir / _package.buildDir / "c"

def buildFfiO : SchedulerM (BuildJob FilePath) := do
  let oFile := cBuildDir / "ffi.o"
  let srcJob ← inputFile <| cSrcDir / "ffi.cpp"
  buildFileAfterDep oFile srcJob fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
    compileO "ffi.c" oFile srcFile flags "c++"

extern_lib libleanffi := do
  let name := nameToStaticLib "leanffi"
  buildStaticLib (cBuildDir / name) #[← buildFfiO]
