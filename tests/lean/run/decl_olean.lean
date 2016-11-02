open tactic

run_command do
 env ← get_env,
 o   ← returnopt (env^.decl_olean `add),
 trace "add was defined in the .olean file:",
 trace o
