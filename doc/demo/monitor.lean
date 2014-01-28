rewrite_set simple
add_rewrite Nat::add_comm Nat::add_left_comm Nat::add_assoc Nat::add_zeror : simple
variables a b c : Nat

(*
 function indent(s)
    for i = 1, s:depth()-1 do
       io.write("  ")
    end
 end
 local m = simplifier_monitor(function(s, e)
                                 indent(s)
                                 print("Visit, depth: " .. s:depth() .. ", " .. tostring(e))
                              end,
                              function(s, e, new_e, pr)
                                 indent(s)
                                 print("Step: " .. tostring(e) .. " ===> " .. tostring(new_e))
                              end,
                              function(s, e, new_e, ceq, ceq_id)
                                 -- if ceq_id == name("Nat", "add_assoc") then
                                    indent(s)
                                    print("Rewrite using: " .. tostring(ceq_id))
                                    indent(s)
                                    print("  " .. tostring(e) .. " ===> " .. tostring(new_e))
                                 -- end
                              end
 )
 local s = simplifier("simple", options(), m)
 local t = parse_lean('a + (b + 0) + a')
 print(t)
 print("=====>")
 local t2, pr = s(t)
 print(t2)
 print(pr)
 get_environment():type_check(pr)
*)
