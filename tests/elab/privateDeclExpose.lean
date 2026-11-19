module

/-! Term `private` should create unexposed bodies regardless of context. -/

def privVal : Nat := 5

@[expose] public def pubVal : Nat := private_decl% privVal

/--
info: @[expose] def pubVal : Nat :=
pubVal._private_1
-/
#guard_msgs in
#print pubVal

-- The aux def must not be `@[expose]`: its body references the private `privVal`.
/--
info: def pubVal._private_1 : Nat :=
privVal
-/
#guard_msgs in
#print pubVal._private_1
