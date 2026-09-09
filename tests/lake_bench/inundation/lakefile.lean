import Lake
open Lake DSL

def test := get_config? test |>.getD "Test" |>.capitalize
def testName := Lean.Name.mkSimple test
def layers := get_config? layers >>= (·.toNat?) |>.getD 20
def width := get_config? width >>= (·.toNat?) |>.getD 20
def precompile := get_config? precompile >>= envToBool? |>.getD false

package inundation where
  buildDir := defaultBuildDir / test

@[default_target]
lean_lib Inundation where
  srcDir := "test"
  roots := #[testName]
  precompileModules := precompile

/- Vary the number of libraries (e.g., for precompilation) -/
section

partial def num2letters (n : Nat) : String :=
  if n >= 26 then
    num2letters (n / 26 - 1) ++ num2letters (n % 26)
  else
    Char.toString <| .ofNat <| 'A'.toNat + n

def testRoots (lo hi : Nat) :=
  (lo...(min hi layers)).toArray.map (testName.str ∘ num2letters)

lean_lib InundationD where
  srcDir := "test"
  roots := testRoots 0 4
  precompileModules := precompile

meta if layers > 4 then
lean_lib InundationH where
  srcDir := "test"
  roots := testRoots 4 8
  precompileModules := precompile

meta if layers > 8 then
lean_lib InundationL where
  srcDir := "test"
  roots := testRoots 8 12
  precompileModules := precompile

meta if layers > 12 then
lean_lib InundationP where
  srcDir := "test"
  roots := testRoots 12 16
  precompileModules := precompile

meta if layers > 16 then
lean_lib InundationT where
  srcDir := "test"
  roots := testRoots 16 20
  precompileModules := precompile

meta if layers > 20 then
lean_lib InundationY where
  srcDir := "test"
  roots := testRoots 20 24
  precompileModules := precompile

end

script nop :=
  return 0

/--
Generate multiple configurations for the configuration test.

USAGE:
  lake run mkTree [<num>]
-/
script mkTree (args : List String) := do
  let some numPkgs := if h : args.length > 0 then args[0].toNat? else some 10
    | return 1
  let wsDir := (← getWorkspace).dir
  let treeDir := wsDir / "test" / "tree"
  let config ← IO.FS.readFile (wsDir / "lakefile.lean")
  let mut depsConfig := config ++ "\n"
  for i in *...numPkgs do
    let pkgName := num2letters i
    let config := config.replace "inundation" pkgName
    let pkgDir := treeDir / pkgName
    IO.FS.createDirAll pkgDir
    IO.FS.writeFile (pkgDir / "lakefile.lean") config
    depsConfig := depsConfig ++ s!"require {pkgName} from \"{pkgName}\"\n"
  IO.FS.writeFile (treeDir / "lakefile.lean") depsConfig
  return 0

/--
Generate imports for a build test.

USAGE:
  lake run [-Ktest=<dir>] [-Klayers=<n>] [-Kwidth=<n>] mkBuild
-/
script mkBuild := do
  let mkImportsFor (layer : Nat) := Id.run do
    let mut out := ""
    for idx in *...width do
      out := out ++ s!"import {test}.{num2letters layer}.M{idx}\n"
    return out
  let mkImportsAt (layer : Nat) :=
    if let .succ prev := layer then mkImportsFor prev else ""

  let testDir := (← getWorkspace).dir / "test"
  try
    IO.FS.removeDirAll (testDir / test)
  catch
    | .noFileOrDirectory .. => pure ()
    | e => throw e
  IO.FS.createDirAll (testDir / test)
  for layer in *...layers do
    let layerDir := testDir / test / num2letters layer
    IO.FS.createDir layerDir
    IO.FS.writeFile (layerDir.addExtension "lean") (mkImportsFor layer)
    for idx in *...width do
      IO.FS.writeFile (layerDir / s!"M{idx}.lean") (mkImportsAt layer)
  IO.FS.writeFile (testDir / s!"{test}.lean") (mkImportsAt layers)

  return 0
