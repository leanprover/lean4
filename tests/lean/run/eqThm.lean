def f : Nat → Bool → Nat
  | 0,  true  => 1
  | 0,  false => 2
  | 1,  true => 3
  | 1,  _ => 4
  | x+2, true => f x true
  | x+2, b => f x (not b)

theorem f_main_eq : f x b = f.match_1 (fun _ _ => Nat) x b (fun _ => 1) (fun _ => 2) (fun _ => 3) (fun _ => 4) (fun x => f x true) (fun x b => f x (not b)) := by
  split
  anyGoals rfl
  conv => lhs; delta f; whnf; simpMatch
  conv => lhs; delta f; whnf; simpMatch
  set_option smartUnfolding false in rfl

#check @f_main_eq
