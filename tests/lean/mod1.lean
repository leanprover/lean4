import specialfn
import specialfn
(*
   local env = environment() -- create new environment
   parse_lean_cmds([[
      import specialfn
      import specialfn
      check sin
   ]], env)
*)
check sin