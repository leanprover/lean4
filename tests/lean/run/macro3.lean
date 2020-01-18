new_frontend

syntax "call" term:max "(" (sepBy1 term ",") ")" : term

macro_rules
| `(call $f ($args*)) => `($f $(args.getEvenElems)*)

#check call Nat.add (1+2, 3)
