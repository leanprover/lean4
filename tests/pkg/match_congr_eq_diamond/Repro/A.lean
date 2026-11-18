inductive T where
  | a | b (n : Nat) | c | d | e

def P : T → Prop
  | .b _ => True
  | _ => False
