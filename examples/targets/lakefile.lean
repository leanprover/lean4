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
target meow : PUnit := Target.opaqueSync (m := BuildM) do
  IO.FS.writeFile (_package.buildDir / "meow.txt") "Meow!"
  return default

target bark : PUnit := Target.opaqueSync (m := BuildM) do
  logInfo "Bark!"
  return default

package_facet print_name : PUnit := fun pkg => do
  IO.println pkg.name
  return ActiveTarget.nil
