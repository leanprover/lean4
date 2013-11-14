
Variables x1 x2 x3 : Bool
Definition F : Bool := x1 /\ (x2 \/ x3)

(**
 local env    = get_environment()
 local F      = env:find_object("F"):get_value()
 print(F)

 function expr_size(e)
    local r = 0
    e:for_each(function(e, offset) r = r + 1 end)
    return r
 end

 print(expr_size(F))

**)

