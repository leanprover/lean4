Variables x y z : Int
Variable f : Int -> Int -> Int

(**
 local t = parse_lean("fun w, f w (f y 0)")
 print(t)
 assert(t:closed())
 local n, d, b = t:fields()
 print(b)
 assert(not b:closed())
 local env = get_environment()
 assert(d == env:find_object("Int"):get_value())
 parse_lean_cmds([[
    Eval 10 + 20
    Check x + y
    Variable g : Int -> Int
 ]])

**)

Check g (f x 10)

