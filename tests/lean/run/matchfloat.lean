def test1 : Nat → Nat
  | 0 => 0
  | _+1 => 42

-- set_option pp.match false

/--
info: test1.match_1.float.{u, v} {α : Sort u} {β : Sort v} (f : α → β) (x✝ : Nat) (h_1 : Unit → (fun x => α) 0)
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

def test2 (α β) : α ∨ β → γ → (β ∨ α) ∧ γ
  | .inl x, y => ⟨.inr x, y⟩
  | .inr x, y => ⟨.inl x, y⟩

set_option pp.proofs true in
/--
info: test2.match_1.float {α β : Prop} (f : α → β) {γ : Prop} (α✝ β✝ : Prop) (x✝ : α✝ ∨ β✝) (x✝¹ : γ)
  (h_1 : ∀ (x : α✝) (y : γ), (fun x x => α) (Or.inl x) y) (h_2 : ∀ (x : β✝) (y : γ), (fun x x => α) (Or.inr x) y) :
  f
      (match x✝, x✝¹ with
      | Or.inl x, y => h_1 x y
      | Or.inr x, y => h_2 x y) =
    match x✝, x✝¹ with
    | Or.inl x, y => f (h_1 x y)
    | Or.inr x, y => f (h_2 x y)
-/
#guard_msgs in
#check test2.match_1.float
