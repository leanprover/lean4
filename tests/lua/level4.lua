assert(not (mk_level_zero() < mk_level_zero()))
local u = mk_global_univ("u")
local v = mk_global_univ("v")
local z   = mk_level_zero()
local max = mk_level_max
local imax = mk_level_imax
local succ = mk_level_succ
assert(max(succ(max(succ(v), u)), max(v, succ(succ(u)))):norm() == max(succ(succ(u)), succ(succ(v))))
assert(imax(succ(succ(max(u, u))), v):norm() == imax(succ(succ(u)), v))
assert(max(u, max(succ(succ(z)), max(u, succ(z)))):norm() == max(succ(succ(z)), u))
