import Int.

(*
 function add_paren(code)
    return "(" .. "* " .. code .. " *" .. ")"
 end
 parse_lean_cmds(add_paren([[
     local env = get_environment()
     env:add_var("x", Const("Int"))
     print(env:find_object("x"))
  ]]))
 print("done")
*)
