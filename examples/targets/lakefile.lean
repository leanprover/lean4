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
target meow (pkg : Package) : Unit := do
  IO.FS.writeFile (pkg.buildDir / "meow.txt") "Meow!"
  return .nil

target bark : Unit := do
  logInfo "Bark!"
  return .nil

package_facet print_name pkg : Unit := do
  IO.println pkg.name
  return .nil
