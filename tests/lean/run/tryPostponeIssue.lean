notation:50 e:51 " matches' " p:51 => (match e with | p => true | _ => false)

def g (x : Nat) := if x + 1 matches' 1 then x else 0
