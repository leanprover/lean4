open nat
definition x [reducible]   := (10:nat)
definition y               := (20:nat)
definition z [irreducible] := (30:nat)
definition w               := (40:nat)


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
 assert(tc:whnf(z) == z)
 -- Only definitions marked as reducible are unfolded
 local tc  = reducible_type_checker(env)
 assert(tc:whnf(x) == val_x)
 assert(tc:whnf(y) == y)
 assert(tc:whnf(z) == z)
 assert(tc:whnf(w) == w)
*)

eval [whnf] x
