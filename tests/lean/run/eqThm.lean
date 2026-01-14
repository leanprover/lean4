def f : Nat → Bool → Nat
  | 0,  true  => 1
  | 0,  false => 2
  | 1,  true => 3
  | 1,  _ => 4
  | x+2, true => f x true
  | x+2, b => f x (not b)

macro "urfl" : tactic => `(tactic| set_option smartUnfolding false in rfl)


theorem f_main_eq : f x b = f.match_1 (fun _ _ => Nat) x b (fun _ => 1) (fun _ => 2) (fun _ => 3) (fun _ => 4) (fun x => f x true) (fun x b => f x (not b)) := by
  split <;> (first | rfl | (conv => lhs; delta f; whnf; simp_match); try urfl)

#check @f_main_eq

def g : List Nat → List Nat → Nat
  | [],         y::ys => y
  | [],         ys    => 0
  | x1::x2::xs, ys    => g xs ys
  | x::xs,      y::ys => g xs ys + y
  | x::xs,      []    => g xs []

theorem g_main_eq (xs ys : List Nat) : g xs ys = g.match_1 (fun _ _ => Nat) xs ys (fun y ys => y) (fun _ => 0) (fun _ _ xs ys => g xs ys) (fun _ xs y ys => g xs ys + y) (fun _ xs => g xs []) := by
  split <;> (first | rfl | (conv => lhs; delta g; whnf; simp_match); try urfl)

#check @g_main_eq

def foo (xs : List Nat) : List Nat :=
  match xs with
  | []    => []
  | x::xs =>
    let y := 2 * x;
    match xs with
    | []    => []
    | x::xs => (y + x) :: foo xs

theorem foo_main_eq (xs : List Nat) : foo xs = foo.match_1 (fun _ => List Nat) xs (fun _ => []) (fun x xs => let y := 2*x; foo.match_1 (fun _ => List Nat) xs (fun _ => []) (fun x xs => (y + x)::foo xs)) := by
  split
  · rfl
  · split
    · rfl
    · rfl

#check @foo_main_eq
