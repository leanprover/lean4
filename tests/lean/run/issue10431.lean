inductive L (α : Type u) : Type u where
  | nil : L α
  | cons : α → L α → L α

def L.eq [BEq α] (xs ys : L α) : Bool :=
  match _ : xs.ctorIdx == ys.ctorIdx with
  | false => false
  | true =>
    match xs, ys with
    | .nil, .nil => true
    | .cons x xs, .cons y ys => x == y && xs.eq ys

/--
info: theorem L.eq.eq_def.{u_1} : ∀ {α : Type u_1} [inst : BEq α] (xs ys : L α),
  xs.eq ys =
    match h : xs.ctorIdx == ys.ctorIdx with
    | false => false
    | true =>
      match xs, ys, h with
      | L.nil, L.nil, h => true
      | L.cons x xs, L.cons y ys, h => x == y && xs.eq ys
-/
#guard_msgs in
#print sig L.eq.eq_def
