

axiom TrustMe {p : Prop} : p

def x := (1, 2)
def y := x
@[noinline] def mk (v : Nat) := (v, v+1)

#eval withPtrAddr x (fun a => dbgTrace (">> " ++ toString a) $ fun _ => 0) TrustMe
