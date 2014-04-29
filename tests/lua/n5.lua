assert(not pcall(function() name(mpz(10)) end))
assert(not pcall(function() name(function() return 1 end) end))
assert(name("x", 1):hash() == name("x", 1):hash())
