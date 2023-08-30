import Lake
open Lake DSL

def test := get_config? test |>.getD "Test"

package inundation where
  buildDir := defaultBuildDir / test

@[default_target]
lean_lib Inundation {
  roots := #[.str `Inundation test]
}

script nop :=
  return 0

partial def num2letters (n : Nat) : String :=
  if n >= 26 then
    num2letters (n / 26 - 1) ++ num2letters (n % 26)
  else
    Char.toString <| .ofNat <| 'A'.toNat + n

/--
USAGE:
  lake run [-Ktest=<dir>] mk [<layers>] [<width>]
-/
script mk (args : List String) := do
  let argc := args.length
  let some layers := if h : argc > 0 then args[0].toNat? else some 40
    | return 1
  let some width  := if h : argc > 1 then args[1].toNat? else some 40
    | return 1

  let mkImportsFor (layer : Nat) := Id.run do
    let mut out := ""
    for idx in [:width] do
      out := out ++ s!"import Inundation.{test}.{num2letters layer}{idx}\n"
    return out
  let mkImportsAt (layer : Nat) :=
    if let .succ prev := layer then mkImportsFor prev else ""

  try
    IO.FS.removeDirAll test
  catch
    | .noFileOrDirectory .. => pure ()
    | e => throw e

  let wsDir := (← getWorkspace).dir
  IO.FS.createDirAll (wsDir / "Inundation" / test)
  for layer in [:layers] do
    for idx in [:width] do
      IO.FS.writeFile (wsDir / "Inundation" / test / s!"{num2letters layer}{idx}.lean") <|
        mkImportsAt layer

  IO.FS.writeFile (wsDir / "Inundation" / s!"{test}.lean") (mkImportsAt layers)
  return 0
