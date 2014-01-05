import Int.
variables x y z : Int
variable f : Int -> Int -> Int

(*
 local t = parse_lean("fun w, f w (f y 0)")
 print(t)
 assert(t:closed())
 local n, d, b = t:fields()
 print(b)
 assert(not b:closed())
 local env = get_environment()
 assert(env:find_object("Int"):get_name() == name("Int"))
*)
