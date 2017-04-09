/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import system.io leanpkg.toml
open io io.proc
variable [io.interface]

namespace leanpkg

def exec_cmd (cmd : string) (args : list string) (cwd : option string := none) : io unit := do
let cmdstr := join " " (cmd::args),
io.put_str_ln $ "> " ++
  match cwd with
  | some cwd := "(cd " ++ cwd ++ "; " ++ cmdstr ++ ")"
  | none := cmdstr
  end,
ch ← spawn { cmd := cmd, args := args, cwd := cwd },
exitv ← wait ch,
when (exitv ≠ 0) $ io.fail $
  "external command exited with status " ++ exitv.to_string

end leanpkg
