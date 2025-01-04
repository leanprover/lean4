def g (xs : List α) (ys : List α) :=
  match xs, ys with
  | [], _         => ys
  | _::_::_, [ ]  => []
  | x::xs,   ys   => x :: g xs ys

attribute [simp] g

set_option trace.grind.assert true

/--
info: [grind.assert] (match as, bs with
      | [], x => bs
      | head :: head_1 :: tail, [] => []
      | x :: xs, ys => x :: g xs ys) =
      d
[grind.assert] bs = []
[grind.assert] a₁ :: f 0 = as
[grind.assert] f 0 = a₂ :: f 1
[grind.assert] ¬d = []
[grind.assert] (match a₁ :: a₂ :: f 1, [] with
      | [], x => bs
      | head :: head_1 :: tail, [] => []
      | x :: xs, ys => x :: g xs ys) =
      []
-/
#guard_msgs (info) in
theorem ex (f : Nat → List Nat) : g as bs = d → bs = [] → a₁ :: f 0 = as → f 0 = a₂ :: f 1 → d = [] := by
  unfold g
  grind
