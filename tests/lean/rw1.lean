(*
mk_rewrite_rule_set("rw1")
add_rewrite_rules("rw1", "and_assoc")
add_rewrite_rules("rw1", "and_truer")
show_rewrite_rules("rw1")
*)

scope
   print "new scope"
   (*
     add_rewrite_rules("rw1", "or_assoc")
     enable_rewrite_rules("rw1", "and_assoc", false)
     show_rewrite_rules("rw1")
   *)
end

print "after end of scope"
(*
  show_rewrite_rules("rw1")
*)
