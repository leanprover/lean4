Import Int.
Variable x : Int
SetOption pp::notation false
(**
print(get_options())
**)
Check x + 2
(**
o = get_options()
o = o:update(name('lean', 'pp', 'notation'), true)
set_options(o)
print(get_options())
**)
Check x + 2
(**
set_option(name('lean', 'pp', 'notation'), false)
print(get_options())
**)
Variable y : Int
Check x + y
