import Lake
open Lake DSL

package targets {
  srcDir := "src"
}

@[defaultTarget]
lean_lib foo
lean_lib bar
lean_lib baz

lean_exe a
lean_exe b

@[defaultTarget]
lean_exe c

@[defaultTarget]
target meow : Unit := fun pkg _ => do
  IO.FS.writeFile (pkg.buildDir / "meow.txt") "Meow!"
  return .nil

target bark : Unit := fun _pkg _ => do
  logInfo "Bark!"
  return .nil

package_facet print_name : Unit := fun pkg _ => do
  IO.println pkg.name
  return .nil
