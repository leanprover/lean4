def foo (rec : Nat → Nat → Nat) : Nat → Nat → Nat
| 0     a := a
| (n+1) a := rec n a + a + rec n (a+1)

partial def fix' (f: (Nat → Nat → Nat) → (Nat → Nat → Nat)) : Nat → Nat → Nat
| a b := f fix' a b

def prof {α : Type} (msg : String) (p : IO α) : IO α :=
let msg := "Time for '" ++ msg ++ "':" in
timeit msg p

def fix_test (n : Nat) : IO Unit :=
IO.println (fix foo n 10)

def fix'_test (n : Nat) : IO Unit :=
IO.println (fix' foo n 10)

def main (xs : List String) : IO Unit :=
prof "native fix" (fix_test xs.head.toNat) *>
prof "fix in lean" (fix'_test xs.head.toNat) *>
pure ()
