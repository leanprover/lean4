syntax "call" term:max "(" sepBy1(term, ",") ")" : term

macro_rules
| `(call $f ($args,*)) => `($f $args*)

/-- info: (1 + 2).add 3 : Nat -/
#guard_msgs in
#check call Nat.add (1+2, 3)
