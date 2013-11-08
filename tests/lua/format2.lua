f = format(format("hello"):highlight('red'), line(), 1):group() .. space() .. (line() .. format("world")):nest(4)
assert(is_format(f))
assert(not is_format("hello"))
assert(not is_format(sexpr(10, 20)))
