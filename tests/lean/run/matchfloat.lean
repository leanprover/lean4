def test1 : Nat → Nat
  | 0 => 0
  | _+1 => 42

-- set_option pp.match false
#check test1.match_1

/--
warning: declaration uses 'sorry'
---
info: test1.match_1.float.{u, v} (α : Sort u) (β : Sort v) (f : α → β) (x✝ : Nat) (h_1 : Unit → (fun x => α) 0)
  (h_2 : (n : Nat) → (fun x => α) n.succ) :
  f
      (match x✝ with
      | 0 => h_1 ()
      | n.succ => h_2 n) =
    match x✝ with
    | 0 => f (h_1 ())
    | n.succ => f (h_2 n)
-/
#guard_msgs in
#check test1.match_1.float

def test2 (α β) : α ∨ β → β ∨ α
  | .inl x => .inr x
  | .inr x => .inl x

set_option pp.proofs true in
/--
warning: declaration uses 'sorry'
---
info: test2.match_1.float (α β : Prop) (f : α → β) (α✝ β✝ : Prop) (x✝ : α✝ ∨ β✝) (h_1 : ∀ (x : α✝), (fun x => α) (Or.inl x))
  (h_2 : ∀ (x : β✝), (fun x => α) (Or.inr x)) :
  f
      (match x✝ with
      | Or.inl x => h_1 x
      | Or.inr x => h_2 x) =
    match x✝ with
    | Or.inl x => f (h_1 x)
    | Or.inr x => f (h_2 x)
-/
#guard_msgs in
#check test2.match_1.float
