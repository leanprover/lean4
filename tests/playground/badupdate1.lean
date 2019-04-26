structure S :=
(vals : Array Nat) (sz : Nat)

@[noinline] def inc0 (a : Array Nat) : Array Nat :=
a.modify 0 (+1)

set_option pp.implicit true
-- set_option trace.compiler.boxed true

def f1 (s : S) : S :=
{ vals := inc0 s.vals, .. s}

def f2 : S → S
| ⟨vals, sz⟩ := ⟨inc0 vals, sz⟩

def test (f : S → S) (n : Nat): IO Unit :=
let s : S := { vals := mkArray (n*100) n, sz := n*100 } in
let s     := n.repeat f s in
IO.println (s.vals.get 0)

def main (xs : List String) : IO Unit :=
timeit "test1" (test f1 xs.head.toNat) *>
timeit "test2" (test f2 xs.head.toNat)
