/-!
Regression test for #15640: `grind` overflowed the stack on a `match` when the
discriminant is in a cyclic equivalence class such as `as = a :: as`.
-/

example (a : Nat) (as : List Nat) (h : as = a :: as) :
    (match as with | 1 :: _ => 1 | _ => 2) > 0 := by
  grind

example (a b : Nat) (xs ys : List Nat) (h1 : xs = a :: ys) (h2 : ys = b :: xs) :
    (match xs with | 1 :: _ => 1 | _ => 2) > 0 := by
  grind

def f : List Nat → Nat
  | 1 :: _ => 1
  | _ => 2

example (a : Nat) (as : List Nat) (h : as = a :: as) : f as > 0 := by
  grind [f.eq_def]

-- The `match`-condition must still be refuted through the cycle.
def g : List Nat → Nat
  | _ :: 1 :: _ => 1
  | _ :: _ :: _ => 2
  | _ => 0

example (as : List Nat) (h : as = 1 :: as) : g as = 1 := by
  grind [g.eq_def]

example (a : Nat) (as : List Nat) (h : as = a :: as) : g as > 0 := by
  grind [g.eq_def]
