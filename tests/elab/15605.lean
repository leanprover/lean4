/-!
Regression test for #15605.
`grind` does not support floats yet. It expects interpreted values to have a unique normal form,
but there are no simprocs for normalizing float literals. Thus, float literals such as `2`, `2.0`,
and `2.00` were treated as different values, and incorrect proofs were generated.
-/

example : True := by
  fail_if_success have : (2 : Float) ≠ 2.0 := by grind
  trivial

example : True := by
  fail_if_success have : (2 : Float32) ≠ 2.0 := by grind
  trivial

example : True := by
  fail_if_success have : (2.0 : Float) ≠ 2.00 := by grind
  trivial

example : True := by
  fail_if_success have : (0.3 : Float) ≠ 0.30000000000000001 := by grind
  trivial

example (x : Float) (_ : x = 2) (_ : x = 2.0) : True := by
  fail_if_success have : False := by grind
  trivial

def f (x : Float) : Nat :=
  match x with
  | 2.0 => 1
  | _ => 0

example : True := by
  fail_if_success have : f 2 = 0 := by grind [f]
  trivial

-- `Float` terms are still handled as uninterpreted terms.
example (x y : Float) (g : Float → Nat) (h₁ : x = 2.0) (h₂ : y = x) : g y = g 2.0 := by
  grind
