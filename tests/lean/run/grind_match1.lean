def g (xs : List α) (ys : List α) :=
  match xs, ys with
  | [], _         => ys
  | _::_::_, [ ]  => []
  | x::xs,   ys   => x :: g xs ys

attribute [simp] g

set_option trace.grind.assert true
set_option trace.grind.split.candidate true
set_option trace.grind.split.resolved true

/--
info: [grind.assert] (match as, bs with
      | [], x => bs
      | head :: head_1 :: tail, [] => []
      | x :: xs, ys => x :: g xs ys) =
      d
[grind.split.candidate] match as, bs with
    | [], x => bs
    | head :: head_1 :: tail, [] => []
    | x :: xs, ys => x :: g xs ys
[grind.assert] bs = []
[grind.assert] a₁ :: f 0 = as
[grind.assert] f 0 = a₂ :: f 1
[grind.assert] ¬d = []
[grind.assert] (match a₁ :: a₂ :: f 1, [] with
      | [], x => bs
      | head :: head_1 :: tail, [] => []
      | x :: xs, ys => x :: g xs ys) =
      []
[grind.split.resolved] match as, bs with
    | [], x => bs
    | head :: head_1 :: tail, [] => []
    | x :: xs, ys => x :: g xs ys
-/
#guard_msgs (info) in
example (f : Nat → List Nat) : g as bs = d → bs = [] → a₁ :: f 0 = as → f 0 = a₂ :: f 1 → d = [] := by
  unfold g
  grind


example : g as bs = d → as = [] → d = bs := by
  unfold g
  grind

def f (x : List α) : Bool :=
  match x with
  | [] => true
  | _::_ => false

example : f a = b → a = [] → b = true := by
  unfold f
  grind

def f' (x : List Nat) : Bool :=
  match x with
  | [] => true
  | _::_ => false

attribute [simp] f'
#check f'.match_1.eq_1

example : f' a = b → a = [] → b = true := by
  unfold f'
  grind
