def inc (r : io.ref nat) : io unit :=
do v ← r.read,
   r.write (v+1),
   io.println (">> " ++ to_string v)

def init_array (r : io.ref (array nat)) (n : nat) : io unit :=
n.mrepeat $ λ i, do
  r.modify $ λ a, a.push (2*i)

def show_array_ref (r : io.ref (array nat)) : io unit :=
do a ← r.swap array.nil,
   a.size.mrepeat (λ i, io.println ("[" ++ to_string i ++ "]: " ++ to_string (a.read' i))),
   r.swap a,
   pure ()

def main (xs : list string) : io unit :=
do let n := xs.head.to_nat,
   r₁ ← io.mk_ref 0,
   n.mrepeat (λ _, inc r₁),
   r₂ ← io.mk_ref (array.nil : array nat),
   init_array r₂ n,
   show_array_ref r₂
