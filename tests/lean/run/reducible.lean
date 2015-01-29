definition x [reducible]   := 10
definition y               := 20
definition z [irreducible] := 30
opaque definition w        := 40

(*
 local env   = get_env()
 local x     = Const("x")
 local y     = Const("y")
 local z     = Const("z")
 local w     = Const("w")
 local val_x = env:find("x"):value()
 local val_y = env:find("y"):value()
 local val_z = env:find("z"):value()
 local val_w = env:find("w"):value()
 -- All definitions are not unfolded
 local tc    = opaque_type_checker(env)
 assert(tc:whnf(x) == x)
 assert(tc:whnf(y) == y)
 assert(tc:whnf(z) == z)
 assert(tc:whnf(w) == w)
 -- Opaque and definitions marked as irreducibled are not unfolded
 local tc  = non_irreducible_type_checker(env)
 assert(tc:whnf(x) == val_x)
 assert(tc:whnf(y) == val_y)
 assert(tc:whnf(z) == z)
 assert(tc:whnf(w) == w)
 -- Only definitions marked as reducible are unfolded
 local tc  = reducible_type_checker(env)
 assert(tc:whnf(x) == val_x)
 assert(tc:whnf(y) == y)
 assert(tc:whnf(z) == z)
 assert(tc:whnf(w) == w)
 -- Default: only opaque definitions are not unfolded.
 -- Opaqueness is a feature of the kernel.
 local tc  = type_checker(env)
 assert(tc:whnf(x) == val_x)
 assert(tc:whnf(y) == val_y)
 assert(tc:whnf(z) == val_z)
 assert(tc:whnf(w) == w)
*)

(*
  local env = get_env()
  assert(is_reducible_on(env, "x"))
  assert(not is_reducible_on(env, "y"))
  assert(not is_reducible_on(env, "z"))
  assert(not is_reducible_off(env, "x"))
  assert(not is_reducible_off(env, "y"))
  assert(is_reducible_off(env, "z"))
  env = set_reducible(env, "x", reducible_status.Off)
  assert(not is_reducible_on(env, "x"))
  assert(is_reducible_off(env, "x"))
  env = set_reducible(env, "x", reducible_status.None)
  assert(not is_reducible_on(env, "x"))
  assert(not is_reducible_off(env, "x"))
  env = set_reducible(env, "x", reducible_status.On)
  assert(is_reducible_on(env, "x"))
  assert(not is_reducible_off(env, "x"))
  env = set_reducible(env, "x", reducible_status.Off)
  set_env(env)
*)

eval [whnf] x
