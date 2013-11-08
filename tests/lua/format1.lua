

f = format(format("hello"):highlight('red'), line(), 1):group() .. space() .. (line() .. format("world")):nest(4)
print(f)
