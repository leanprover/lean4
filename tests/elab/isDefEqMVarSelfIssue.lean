
partial def f : Bool :=
let rec loop (i : Nat) :=
  let v := true
  if v = v then loop (i+1) else v
loop 1

set_option pp.all true

#print f.loop._unsafe_rec
