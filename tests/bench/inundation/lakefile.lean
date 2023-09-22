import Lake
open Lake DSL

def test := get_config? test |>.getD "Test" |>.capitalize

package inundation where
  buildDir := defaultBuildDir / test

@[default_target]
lean_lib Inundation where
  srcDir := "test"
  roots := #[test]

script nop :=
  return 0

partial def num2letters (n : Nat) : String :=
  if n >= 26 then
    num2letters (n / 26 - 1) ++ num2letters (n % 26)
  else
    Char.toString <| .ofNat <| 'A'.toNat + n

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
  for i in [:numPkgs] do
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
  lake run [-Ktest=<dir>] mkBuild [<layers>] [<width>]
-/
script mkBuild (args : List String) := do
  let argc := args.length
  let some layers := if h : argc > 0 then args[0].toNat? else some 40
    | return 1
  let some width  := if h : argc > 1 then args[1].toNat? else some 40
    | return 1

  let mkImportsFor (layer : Nat) := Id.run do
    let mut out := ""
    for idx in [:width] do
      out := out ++ s!"import {test}.{num2letters layer}{idx}\n"
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
  for layer in [:layers] do
    for idx in [:width] do
      IO.FS.writeFile (testDir / test / s!"{num2letters layer}{idx}.lean") <|
        mkImportsAt layer
  IO.FS.writeFile (testDir / s!"{test}.lean") (mkImportsAt layers)

  return 0
