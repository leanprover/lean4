axiom TrustMe {p : Prop} : p

def x := (1, 2)
def y := x
@[noinline] def mk (v : Nat) := (v, v+1)

#eval withPtrAddr x (fun a => dbgTrace (">> " ++ toString a) $ fun _ => 0) TrustMe
#eval withPtrEq (fun a b => dbgTrace (">> " ++ toString a ++ " == " ++ toString b) $ fun _ => a == b) TrustMe x y -- should not print message
#eval withPtrEq (fun a b => dbgTrace (">> " ++ toString a ++ " == " ++ toString b) $ fun _ => a == b) TrustMe x (mk 1) -- should print message
