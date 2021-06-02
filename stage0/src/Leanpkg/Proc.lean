/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich
-/
namespace Leanpkg

def execCmd (args : IO.Process.SpawnArgs) : IO Unit := do
  let envstr := String.join <| args.env.toList.map fun (k, v) => s!"{k}={v.getD ""} "
  let cmdstr := " ".intercalate (args.cmd :: args.args.toList)
  IO.eprintln <| "> " ++ envstr ++
    match args.cwd with
    | some cwd => s!"{cmdstr}    # in directory {cwd}"
    | none     => cmdstr
  let child ← IO.Process.spawn args
  let exitCode ← child.wait
  if exitCode != 0 then
    throw <| IO.userError <| s!"external command exited with status {exitCode}"

end Leanpkg
