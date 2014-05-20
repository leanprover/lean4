local l = max_univ()
assert(l == mk_level_zero())
assert(l == max_univ(l))
local l1 = param_univ("l1")
local l2 = param_univ("l2")
assert(max_univ(l1, l2):is_geq(max_univ(l2, l1)))
assert(max_univ(l1+1, l2+1):is_geq(max_univ(l2, l1)+1))
-- is_geq_core assumes the levels are normalized
assert(not max_univ(l1+1, l2+1):is_geq_core(max_univ(l2, l1)+1))

