universe M1 >= 1
universe M2 >= 1
universe Z >= max M1+1 M2+1
print environment
(*
local env = get_environment()
assert(env:get_universe_distance("Z", "M1") == 1)
assert(env:get_universe_distance("Z", "M2") == 1)
*)
