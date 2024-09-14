mutual
def g (i j : Nat) : Nat :=
  if i < 5 then 0 else
  match j with
  | Nat.zero => 1
  | Nat.succ j => h i j
termination_by (i + j, 0)
decreasing_by
  · apply Prod.Lex.left
    apply Nat.lt_succ_self

def h (i j : Nat) : Nat :=
  match j with
  | 0 => g i 0
  | Nat.succ j => g i j
termination_by (i + j, 1)
decreasing_by
  · apply Prod.Lex.right
    decide
  · apply Prod.Lex.left
    apply Nat.lt_succ_self
end

/-- info: g.eq_1 (i : Nat) : g i Nat.zero = if i < 5 then 0 else 1 -/
#guard_msgs in
#check g.eq_1

/-- info: g.eq_2 (i j_2 : Nat) : g i j_2.succ = if i < 5 then 0 else h i j_2 -/
#guard_msgs in
#check g.eq_2

/--
info: g.eq_def (i j : Nat) :
  g i j =
    if i < 5 then 0
    else
      match j with
      | Nat.zero => 1
      | j.succ => h i j
-/
#guard_msgs in
#check g.eq_def

/-- error: unknown identifier 'g.eq_3' -/
#guard_msgs in
#check g.eq_3

/-- info: h.eq_1 (i : Nat) : h i 0 = g i 0 -/
#guard_msgs in
#check h.eq_1

/-- info: h.eq_2 (i j_2 : Nat) : h i j_2.succ = g i j_2 -/
#guard_msgs in
#check h.eq_2

/--
info: h.eq_def (i j : Nat) :
  h i j =
    match j with
    | 0 => g i 0
    | j.succ => g i j
-/
#guard_msgs in
#check h.eq_def

/-- error: unknown identifier 'h.eq_3' -/
#guard_msgs in
#check h.eq_3
