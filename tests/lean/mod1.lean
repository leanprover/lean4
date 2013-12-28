Import simple
Import simple
(**
   local env = environment() -- create new environment
   parse_lean_cmds([[
      Import "simple.lean"
      Import "simple.lean"
      Check x + y
      Variable z : Int
      Check z
   ]], env)
   -- Remark: z is not defined in the main environment
**)
Check z