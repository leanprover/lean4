local macro (name := hi) "test1" : term => `(42)
local macro (name := hi.there) "test2" : term => `(42)
local macro (name := hi.there.more) "test3" : term => `(42)
local macro (name := hi.there.more.yes) "test4" : term => `(42)

#check test1
#check test2
#check test3
#check test4
