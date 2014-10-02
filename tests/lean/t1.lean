(*
print("testing...")
local env = get_env()
env = add_decl(env, mk_constant_assumption("x", Prop))
assert(env:find("x"))
set_env(env)
*)

(*
local env = get_env()
print(env:find("x"):type())
*)
