mutual
  def f : Nat → α → α → α
    | 0, a, b => a
    | n, a, b => g a n b |>.1
  termination_by n _ _ => (n, 2)
  decreasing_by
    apply Prod.Lex.right
    decide

  def g : α → Nat → α → (α × α)
    | a, 0, b => (a, b)
    | a, n, b => (h a b n, a)
  termination_by _ n _ => (n, 1)
  decreasing_by
    apply Prod.Lex.right
    decide

  def h : α → α → Nat → α
    | a, b, 0 => b
    | a, b, n+1 => f n a b
  termination_by _ _ n => (n, 0)
  decreasing_by
    apply Prod.Lex.left
    apply Nat.lt_succ_self
end

/-- info: 'a' -/
#guard_msgs in
#eval f 5 'a' 'b'

/-- info: @f.eq_1 : ∀ {α : Type u_1} (x x_1 : α), f 0 x x_1 = x -/
#guard_msgs in
#check @f.eq_1
/--
info: @f.eq_2 : ∀ {α : Type u_1} (x : Nat) (x_1 x_2 : α), (x = 0 → False) → f x x_1 x_2 = (g x_1 x x_2).fst
-/
#guard_msgs in
#check @f.eq_2
/--
info: @f.eq_def : ∀ {α : Type u_1} (x : Nat) (x_1 x_2 : α),
  f x x_1 x_2 =
    match x, x_1, x_2 with
    | 0, a, b => a
    | n, a, b => (g a n b).fst
-/
#guard_msgs in
#check @f.eq_def
/-- error: unknown identifier 'f.eq_3' -/
#guard_msgs in
#check @f.eq_3

/-- info: @h.eq_1 : ∀ {α : Type u_1} (x x_1 : α), h x x_1 0 = x_1 -/
#guard_msgs in
#check @h.eq_1
/-- info: @h.eq_2 : ∀ {α : Type u_1} (x x_1 : α) (n : Nat), h x x_1 n.succ = f n x x_1 -/
#guard_msgs in
#check @h.eq_2
/--
info: @h.eq_def : ∀ {α : Type u_1} (x x_1 : α) (x_2 : Nat),
  h x x_1 x_2 =
    match x, x_1, x_2 with
    | a, b, 0 => b
    | a, b, n.succ => f n a b
-/
#guard_msgs in
#check @h.eq_def

/-- error: unknown identifier 'h.eq_3' -/
#guard_msgs in
#check @h.eq_3
