import system.io

section


def tst_io : io string :=
do b ← io.fs.read_file "tactic_io.lean",
   return b^.to_string
end

open tactic
meta def tac : tactic unit :=
do s ← tactic.unsafe_run_io tst_io,
   trace s

run_cmd tac
