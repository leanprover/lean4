(**
macro("MyMacro", { macro_arg.Expr, macro_arg.Comma, macro_arg.Expr },
     function (env, e1, e2)
        return Const({"Int", "add"})(e1, e2)
     end)
macro("Sum", { macro_arg.Exprs },
      function (env, es)
         if #es == 0 then
            return iVal(0)
         end
         local r   = es[1]
         local add = Const({"Int", "add"})
         for i = 2, #es do
            r = add(r, es[i])
         end
         return r
      end)
**)

Show (MyMacro 10, 20) + 20
Show (Sum)
Show Sum 10 20 30 40
Show fun x, Sum x 10 x 20
Eval (fun x, Sum x 10 x 20) 100
