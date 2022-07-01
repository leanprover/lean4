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
target meow : PUnit := fun pkg => do
  IO.FS.writeFile (pkg.buildDir / "meow.txt") "Meow!"
  return ActiveTarget.nil

target bark : PUnit := fun _ => do
  logInfo "Bark!"
  return ActiveTarget.nil

package_facet print_name : PUnit := fun pkg => do
  IO.println pkg.name
  return ActiveTarget.nil
