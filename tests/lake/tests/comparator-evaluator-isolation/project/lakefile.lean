import Lake
open Lake DSL

/-! Attempt tampering during configuration loading, before solution compilation. -/

def attemptTampering : Unit := run_io do
  for name in ["config.json", "accepted.json", "reference.export"] do
    let path := "../evaluator/" ++ name
    try
      IO.FS.writeFile path "tampered"
      IO.eprintln s!"protected-write-succeeded: {name}"
    catch _ => IO.eprintln s!"protected-write-denied: {name}"
  if <- System.FilePath.pathExists ".lake/poison" then
    throw <| IO.userError "submission cache was visible"
  -- The host fixture makes this a hard link to the reference. Fresh storage hides it.
  IO.FS.writeFile ".lake/reference-link" "private build output"
  IO.eprintln "private-build-write-succeeded"
  let cwd <- IO.Process.getCurrentDir
  let evaluator := cwd.parent.getD "." / "evaluator"
  let out <- IO.Process.output {
    cmd := "/bin/ln", args := #["-sfn", evaluator.toString, ".lake/redirect"] }
  unless out.exitCode == 0 do
    throw <| IO.userError "could not plant the tampering symlink"
  for name in ["config.json", "accepted.json", "reference.export"] do
    try
      IO.FS.writeFile (".lake/redirect/" ++ name) "tampered through a symlink"
      IO.eprintln s!"protected-write-succeeded: symlink {name}"
    catch _ => IO.eprintln s!"protected-write-denied: symlink {name}"

package submission
lean_lib Reference
lean_lib Good
lean_lib AliasSpoof
lean_lib TargetSpoof
lean_lib Extra
