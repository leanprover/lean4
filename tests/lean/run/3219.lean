inductive Tree (α : Type u) : Nat → Type u
  | leaf : Tree α 0
  | branch :
    (val : α)
    → (left : Tree α n)
    → (right : Tree α m)
    → Tree α (n+m+1)

def popLast {α : Type u} (heap : Tree α (o+1)) : (α × Tree α o) :=
  match o, heap with
  | (n+m), .branch a (left : Tree α n) (right : Tree α m)  =>
    if r : m = 0 then
      --remove left
      match n, left with
      | 0, _ => (a, (Eq.symm $ r.subst $ Nat.zero_add m : 0=0+m)▸Tree.leaf)
      | (l+1), left =>
        let (res, (newLeft : Tree α l)) := popLast left
        (res, (Nat.add_right_comm l m 1)▸Tree.branch a newLeft right)
    else
      --remove right
      match  m, right with
      | (r+1), right =>
        let (res, (newRight : Tree α r)) := popLast right
        (res, Tree.branch a left newRight)

def SomePredicate (_ : Tree α n) : Prop := True

/--
info: equations:
theorem popLast.eq_1.{u} : ∀ {α : Type u} (n m : Nat) (a : α) (left : Tree α n) (right : Tree α m),
  popLast (Tree.branch a left right) =
    if r : m = 0 then
      match n, left with
      | 0, x => (a, ⋯ ▸ Tree.leaf)
      | l.succ, left =>
        match popLast left with
        | (res, newLeft) => (res, ⋯ ▸ Tree.branch a newLeft right)
    else
      match m, right, r with
      | r.succ, right, r_1 =>
        match popLast right with
        | (res, newRight) => (res, Tree.branch a left newRight)
-/
#guard_msgs in
#print equations popLast
