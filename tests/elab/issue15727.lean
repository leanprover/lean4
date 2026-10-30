/-!
Regression test for #15727: structural recursion did not translate recursive calls in the
discriminants of a `match` whose alternatives also recurse, and the resulting kernel error was
not caught under `Elab.async`, so there was no fallback to well-founded recursion.
-/

def f : List Nat → Nat
  | [] => 0
  | x :: xs => match xs, f xs with
    | [], r => r + x
    | _ :: ys, r => r + f ys

def g : List Nat → Nat
  | [] => 0
  | x :: xs => match xs, g xs with
    | [], r => r + x
    | _ :: ys, r => r + g ys
termination_by structural xs => xs

example : f [1, 2, 3] = 6 := by decide
example : g [1, 2, 3] = f [1, 2, 3] := rfl

example (x y : Nat) (ys : List Nat) : f (x :: y :: ys) = f (y :: ys) + f ys := by
  simp [f]
