module

/-!
Exercises end-to-end ARM64 code generation for calls, control flow, closures,
constructors, stack arguments, and floating-point values.
-/

inductive Pair where
  | mk : Nat → Nat → Pair

@[noinline] def sumPair : Pair → Nat
  | .mk x y => x + y

@[noinline] def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

@[noinline] def sumNine (a b c d e f g h i : Nat) : Nat :=
  a + b + c + d + e + f + g + h + i

@[noinline] def applyCaptured (base : Nat) (x : Nat) : Nat :=
  (fun y => base + y) x

@[noinline] def addFloat (x y : Float) : Float :=
  x + y

def run : IO Unit := do
  IO.println (sumPair (.mk 20 22))
  IO.println (factorial 5)
  IO.println (sumNine 1 2 3 4 5 6 7 8 9)
  IO.println (applyCaptured 10 7)
  IO.println (addFloat 1.5 2.25)

def main : IO Unit :=
  run

@[export lean_native_backend_test_main]
def exportedMain : IO Unit :=
  run
