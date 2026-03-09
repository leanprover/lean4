

axiom TrustMe {p : Prop} : p

def x := (1, 2)
def y := x
@[noinline] def mk (v : Nat) := (v, v+1)

#eval withPtrAddr x (fun a => dbgTrace (">> " ++ toString a) $ fun _ => 0) TrustMe

/-- info: true -/
#guard_msgs in
#eval withPtrEq x y (fun _ => dbgTrace (">> " ++ toString x ++ " == " ++ toString y) $ fun _ => x == y) TrustMe -- should not print message

/--
info: >> (1, 2) == (1, 2)
---
info: true
-/
#guard_msgs in
#eval withPtrEq x (mk 1) (fun _ => dbgTrace (">> " ++ toString x ++ " == " ++ toString y) $ fun _ => x == y) TrustMe -- should print message
