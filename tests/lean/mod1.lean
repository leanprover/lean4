import cast
import cast
(*
   local env = environment() -- create new environment
   parse_lean_cmds([[
      import cast
      import cast
      check @cast
   ]], env)
*)
check @cast