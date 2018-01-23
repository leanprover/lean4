/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import system.io leanpkg.toml
open io io.proc

namespace leanpkg

def exec_cmd (args : io.process.spawn_args) : io unit := do
let cmdstr := join " " (args.cmd :: args.args),
io.put_str_ln $ "> " ++
  match args.cwd with
  | some cwd := cmdstr ++ "    # in directory " ++ cwd
  | none := cmdstr
  end,
ch ← spawn args,
exitv ← wait ch,
when (exitv ≠ 0) $ io.fail $
  "external command exited with status " ++ repr exitv

def change_dir (dir : string) : io unit := do
io.put_str_ln sformat!"> cd {dir}",
io.env.set_cwd dir

end leanpkg
