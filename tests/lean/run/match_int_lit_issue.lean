theorem Int.eq_zero_of_sign_eq_zero' : ∀ {a : Int}, sign a = 0 → a = 0
  | 0, _ => rfl

def foo (a : Int) : Bool :=
  match a with
  | Int.ofNat 0 => true
  | Int.ofNat 1 => true
  | _ => false

example : ∀ {a : Int}, foo a = true → a = 0 ∨ a = 1
  | 0, _ => Or.inl rfl
  | 1, _ => Or.inr rfl
