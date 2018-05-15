import system.io
import init.lean.ir.lirc
open lean.ir io

def main : io unit :=
do args ← io.cmdline_args,
   unless (args.length = 1) $
     io.fail "Error: incorrect number of arguments, expected `lirc file.lean`",
   let fname := args.head,
   input ← fs.read_file fname,
   match lirc input {main_proc := some "main"} with
   | except.ok r    := fs.write_file (fname ++ ".cpp") r
   | except.error e := io.fail (to_string e)
