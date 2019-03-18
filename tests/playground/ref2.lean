def init_x : io (io.ref nat) :=
io.mk_ref 0

@[init init_x] constant x : io.ref nat := default _

def inc : io unit :=
do v ← x.read,
   x.write (v+1),
   io.println (">> " ++ to_string v)

def main (xs : list string) : io unit :=
do let n := xs.head.to_nat,
   n.mrepeat (λ _, inc)
