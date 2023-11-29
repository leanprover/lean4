import Lake
open Lake DSL

package targets {
  srcDir := "src"
}

@[default_target]
lean_lib Foo where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib Bar where
  defaultFacets := #[LeanLib.sharedFacet]

lean_lib Baz where
  extraDepTargets := #[`caw]

lean_exe a
lean_exe b

@[default_target]
lean_exe c

@[default_target]
target meow pkg : Unit := do
  IO.FS.writeFile (pkg.buildDir / "meow.txt") "Meow!"
  return .nil

target caw pkg : Unit := do
  IO.FS.writeFile (pkg.buildDir / "caw.txt") "Caw!"
  return .nil

target bark : Unit := do
  logInfo "Bark!"
  return .nil

target bark_bark : Unit := do
  bark.fetch

package_facet print_name pkg : Unit := do
  IO.println pkg.name
  return .nil

module_facet get_src mod : FilePath := do
  inputFile mod.leanFile

module_facet print_src mod : Unit := do
  (← fetch <| mod.facet `get_src).bindSync fun src trace => do
    IO.println src
    return ((), trace)

library_facet print_name lib : Unit := do
  IO.println lib.name
  return .nil
