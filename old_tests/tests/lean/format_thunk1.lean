open tactic

example : true :=
by do
   str ← to_expr ``(string),
   one ← to_expr ``(1),
   definev `H str one,
   constructor
