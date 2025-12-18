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

-- and mutual

mutual
inductive L1 (α : Type u) : Type u where
  | nil : L1 α
  | cons : α → L2 α → L1 α
inductive L2 (α : Type u) : Type u where
  | nil : L2 α
  | cons : α → L1 α → L2 α
end

mutual
def L1.eq [BEq α] (xs ys : L1 α) : Bool :=
  match _ : xs.ctorIdx == ys.ctorIdx with
  | false => false
  | true =>
    match xs, ys with
    | .nil, .nil => true
    | .cons x xs, .cons y ys => x == y && xs.eq ys
def L2.eq [BEq α] (xs ys : L2 α) : Bool :=
  match _ : xs.ctorIdx == ys.ctorIdx with
  | false => false
  | true =>
    match xs, ys with
    | .nil, .nil => true
    | .cons x xs, .cons y ys => x == y && xs.eq ys
end


/--
info: theorem L1.eq.eq_def.{u_1} : ∀ {α : Type u_1} [inst : BEq α] (xs ys : L1 α),
  xs.eq ys =
    match h : xs.ctorIdx == ys.ctorIdx with
    | false => false
    | true =>
      match xs, ys, h with
      | L1.nil, L1.nil, h => true
      | L1.cons x xs, L1.cons y ys, h => x == y && xs.eq ys
-/
#guard_msgs in
#print sig L1.eq.eq_def
/--
info: theorem L2.eq.eq_def.{u_1} : ∀ {α : Type u_1} [inst : BEq α] (xs ys : L2 α),
  xs.eq ys =
    match h : xs.ctorIdx == ys.ctorIdx with
    | false => false
    | true =>
      match xs, ys, h with
      | L2.nil, L2.nil, h => true
      | L2.cons x xs, L2.cons y ys, h => x == y && xs.eq ys
-/
#guard_msgs in
#print sig L2.eq.eq_def
