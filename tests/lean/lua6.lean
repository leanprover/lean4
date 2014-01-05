import Int.
variable x : Int
setoption pp::notation false
(*
print(get_options())
*)
check x + 2
(*
o = get_options()
o = o:update(name('lean', 'pp', 'notation'), true)
set_options(o)
print(get_options())
*)
check x + 2
(*
set_option(name('lean', 'pp', 'notation'), false)
print(get_options())
*)
variable y : Int
check x + y
