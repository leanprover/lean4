import system.io
import data.buffer

structure z3_instance [io.interface] : Type :=
  (process : io.proc.child)

def z3_instance.start  [io.interface] : io z3_instance :=
z3_instance.mk <$> io.proc.spawn {
    cmd := "z3",
    args := ["-smt2", "-in"],
    stdin := io.process.stdio.piped,
    stdout := io.process.stdio.piped
}

def z3_instance.raw [io.interface] (z3 : z3_instance) (cmd : string) : io string :=
do let z3_stdin := z3.process.stdin,
   let z3_stdout := z3.process.stdout,
   let cs := cmd.reverse.to_buffer,
   io.fs.write z3_stdin cs,
   io.fs.close z3_stdin,
   -- need read all
   res ← io.fs.read z3_stdout 1024,
   return res.to_string
