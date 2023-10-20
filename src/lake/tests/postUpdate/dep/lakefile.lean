import Lake
open Lake DSL

package dep

lean_exe hello

post_update pkg do
  let wsToolchainFile := (← getRootPackage).dir / "toolchain"
  let depToolchain ← IO.FS.readFile <| pkg.dir / "toolchain"
  IO.FS.writeFile wsToolchainFile depToolchain
  let exeFile ← runBuild hello.build >>= (·.await)
  let exitCode ← env exeFile.toString #["get"]
  if exitCode ≠ 0 then
    error s!"{pkg.name}: failed to fetch hello"
