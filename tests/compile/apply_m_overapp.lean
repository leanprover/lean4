/-!
This is a regression test reproducer for #14969.

Applying more than `closureMaxArgs` arguments at once to a closure of smaller arity used the
array calling convention, which is only correct above that arity, and crashed. `Chain` keeps
every closure at arity 1, and `f` is opaque in `apply20` so that all 20 arguments are applied
in a single `lean_apply_m` call.
-/

abbrev Chain : Nat → Type
  | 0     => Nat
  | n + 1 => Nat → Chain n

def mk : (n : Nat) → Chain n
  | 0     => 42
  | n + 1 => fun _ => mk n

@[noinline] def apply20 (f : Chain 20) : Nat :=
  f 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20

def main : IO Unit :=
  IO.println (apply20 (mk 20))
