import Lake
open Lake DSL

package dep where
  postUpdate? := some do
    let some pkg ← findPackage? `dep
      | error "dep is missing from workspace"
    let wsToolchainFile := (← getRootPackage).dir / "toolchain"
    let depToolchain ← IO.FS.readFile <| pkg.dir / "toolchain"
    IO.FS.writeFile wsToolchainFile depToolchain
    let some exe := pkg.findLeanExe? `hello
      | error s!"{pkg.name}: hello is missing from the package"
    let exeFile ← runBuild (exe.build >>= (·.await))
    let exitCode ← env exeFile.toString #["get"]
    if exitCode ≠ 0 then
      error s!"{pkg.name}: failed to fetch hello"

lean_exe hello
