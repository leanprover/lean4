module
def f (x : Nat) : Nat → Nat → Nat :=
  match x with
  | 0 => fun _ _ => 0
  | _+1 => fun a b => a + b

example : f 0 b c = 0 := by
  grind [f]

example : f (a+1) b c = b + c := by
  grind [f]

example : f x b c ≠ b + c → x = a + 1 → False := by
  grind [f]

example : x = a + 1 → f x b c ≠ b + c → False := by
  grind [f]

example : x = a + 1 → f x b c ≠ b + c → False := by
  grind [f]

example : f x b c > 0 → x = 0 → False := by
  grind [f]

example : f x b c > 0 → x ≠ 0 := by
  grind [f]

example (f : Nat → Nat → Nat) : f 2 3 ≠ 5 → f = (fun x y : Nat => x + y) → False := by
  grind

opaque bla : Nat → Nat → Nat → Nat

/--
trace: [grind.beta] f 2 3 = 2 + 3, using fun x y => x + y
[grind.beta] f 2 3 = bla 2 3 2, using fun x y => bla x y x
-/
#guard_msgs (trace) in
set_option trace.grind.beta true in
example (g h f : Nat → Nat → Nat) :
        f 2 3 ≠ 5 →
          g = (fun x y : Nat => x + y) →
          h = (fun x y => bla x y x) →
          g = h →
          f = h →
          False := by
  grind

example (g h f : Nat → Nat → Nat) :
        f 2 3 ≠ 5 →
          h = (fun x y => bla x y x) →
          g = (fun x y : Nat => x + y) →
          g = h →
          h = f →
          False := by
  grind


example (f : Nat → Nat → Nat) : f = (fun x y : Nat => x + y) → f 2 3 = 5 := by
  grind

example (f g h : Nat → Nat → Nat) :
          h = (fun x y => bla x y x) →
          g = (fun x y : Nat => x + y) →
          g = h →
          h = f →
          f 2 3 = 5 := by
  grind

example (f : Nat → Nat) : f = (fun x : Nat => x + 5) → f 2 > 5 := by
  grind

example (f : Nat → Nat → Nat) : f a = (fun x : Nat => x + 5) → f a 2 > 5 := by
  grind
