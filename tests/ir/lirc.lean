import init.IO
import init.Lean.Ir.lirc
open Lean.Ir IO

def main : IO Unit :=
do args ← IO.cmdlineArgs;
   unless (args.length = 1) $
     IO.fail "Error: incorrect number of arguments, expected `lirc file.Lean`";
   let fname := args.head;
   input ← Fs.readFile fname;
   match lirc input {mainProc := some "main"} with
   | Except.ok r    := Fs.writeFile (fname ++ ".cpp") r
   | Except.error e := IO.fail (toString e)
