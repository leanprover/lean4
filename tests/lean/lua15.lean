Variables i j : Int
Variable p : Bool

(**
 local env = get_environment()
 ok, jst = pcall(
    function()
       print(parse_lean("i + p"))
 end)
 assert(not ok)
 assert(is_justification(jst))
 assert(not jst:is_null())
 print(jst:pp{display_children = false})
**)
