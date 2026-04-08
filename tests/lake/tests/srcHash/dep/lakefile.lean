import Lake
open System Lake DSL

package dep

input_file a where
  path := "a.txt"

target b (pkg) : FilePath := do
  let bFile := pkg.srcDir / "b.txt"
  buildFileAfterDep bFile (← a.fetch) fun a => do
    IO.FS.writeFile bFile ((← IO.FS.readFile a).trimAsciiEnd.copy ++ "b")

@[default_target]
target c (pkg) : FilePath := do
  let cFile := pkg.buildDir / "c.txt"
  buildFileAfterDep cFile (← b.fetch) fun b => do
    createParentDirs cFile
    IO.FS.writeFile cFile ((← IO.FS.readFile b).trimAsciiEnd.copy ++ "c")
