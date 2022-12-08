def mkBigPairs : Nat → Array (Nat × Nat) → Array (Nat × Nat)
| 0     ps := ps
| (n+1) ps := mkBigPairs n (ps.push (n, n))

set_option pp.implicit true
set_option pp.binderTypes false
-- set_option trace.compiler.specialize true
-- set_option trace.compiler.boxed true

def f1 (ps : Array (Nat × Nat)) : Array (Nat × Nat) :=
ps.hmap (λ p,
 -- let p := dbgTraceIfShared "bad1" p in
 { p with fst := p.fst + 1 })

def f2 (ps : Array (Nat × Nat)) : Array (Nat × Nat) :=
ps.map (λ p,
  -- let p := dbgTraceIfShared "bad2" p in
  { p with  fst := p.fst + 1 })


def prof {α : Type} (msg : String) (p : IO α) : IO α :=
let msg₁ := "Time for '" ++ msg ++ "':" in
timeit msg₁ p

def test1 (n : Nat) : IO Unit :=
let m := mkBigPairs n ∅ in
let m := n.repeat f1 m in
let s := m.foldl (λ p n, n + p.1) 0 in
IO.println s

def test2 (n : Nat) : IO Unit :=
let m := mkBigPairs n ∅ in
let m := n.repeat f2 m in
let s := m.foldl (λ p n, n + p.1) 0 in
IO.println s

def main (xs : List String) : IO Unit :=
let n  := xs.head.toNat in
prof "hmap" (test1 n) *>
prof "map"  (test2 n)
