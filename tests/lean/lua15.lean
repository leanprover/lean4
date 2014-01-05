Import Int.
Variables i j : Int
Variable p : Bool

(*
 local env = get_environment()
 ok, ex = pcall(
    function()
       print(parse_lean("i + p"))
 end)
 assert(not ok)
 assert(is_exception(ex))
 print(ex:what())
 ex:rethrow()
*)
