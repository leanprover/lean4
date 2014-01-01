Import Int.
Variables x y z : Int

(**
 import("util.lua")
 local env  = get_environment()
 local plus = Const{"Int", "add"}
 local x, y = Consts("x y")
 local def  = plus(plus(x, y), iVal(1000))
 print(def, ":", env:type_check(def))
 env:add_definition("sum", def)
**)

Eval sum + 3
