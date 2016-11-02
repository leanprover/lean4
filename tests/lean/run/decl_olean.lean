open tactic

run_command do
 env ← get_env,
 o   ← returnopt (env^.decl_olean `add),
 trace "add was defined in the .olean file:",
 trace o

run_command do
 env ← get_env,
 o   ← returnopt (env^.decl_olean `nat.succ),
 trace "nat.succ was defined in the .olean file:",
 trace o

run_command do
 env ← get_env,
 o   ← returnopt (env^.decl_olean `subsingleton.intro),
 trace "subsingleton.intro was defined in the .olean file:",
 trace o

run_command do
 env ← get_env,
 o   ← returnopt (env^.decl_olean `subsingleton.rec),
 trace "subsingleton.rec was defined in the .olean file:",
 trace o

run_command do
 env ← get_env,
 o   ← returnopt (env^.decl_olean `quot),
 trace "quot was defined in the .olean file:",
 trace o
