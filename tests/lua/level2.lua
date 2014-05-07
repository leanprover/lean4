local u = mk_global_univ("u")
assert(is_level(u))
assert(u:is_global())
assert(u:id() == name("u"))
