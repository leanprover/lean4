set_option warn.sorry false

def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)

def ack' : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack' x 1
  | x+1, y+1 => ack' x (ack' (x+1) y)

theorem ack'_eq_ack_works (i x : Nat) : ack' i x = ack i x := by
  fun_induction ack with
  | case1 => sorry
  | case2 => sorry
  | case3 => sorry

theorem ack'_eq_ack_fails : ack' = ack := by
  ext i x
  fun_induction ack with -- Previously: could not find a suitable call of 'ack' in the goal
  | case1 => sorry
  | case2 => sorry
  | case3 => sorry

theorem same_in_lctxt (i x : Nat) : False := by
  have : ack ?i ?x = ack' ?i ?x := sorry
  case i => exact i
  case x => exact x
  fun_induction ack with
  | case1 => sorry
  | case2 => sorry
  | case3 => sorry
