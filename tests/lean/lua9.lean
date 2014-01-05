Import Int.
Variable x : Bool

(*
 import("util.lua")
 local env    = get_environment()
 local Int    = Const("Int")
 local plus   = Const{"Int", "add"}
 local x1, x2 = Consts("x1, x2")
 print(env:type_check(Int))
 print(env:type_check(plus))
 env:add_var("x1", Int)
 env:add_var("x2", Int)
 print(plus(x1, x2))
 print(env:type_check(plus(x1)))

 function sum(...)
    local args = {...}
    if #args == 0 then
       error("sum must have at least one argument")
    else
       local r = args[1]
       for i = 2, #args do
          r = plus(r, args[i])
       end
       return r
    end
 end

 local s = sum(x1, x1, x1, x2, x2)
 print(s)
 print(env:type_check(s))
 env:add_definition("sum1", s)
*)

print Environment 1
Eval sum1
Variable y : Bool
