Import cast
Import cast
(**
   local env = environment() -- create new environment
   parse_lean_cmds([[
      Import cast
      Import cast
      Check @cast
   ]], env)
**)
Check @cast