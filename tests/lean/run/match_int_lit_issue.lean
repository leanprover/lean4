set_option match.sparseCases false -- TODO
-- set_option trace.Meta.Match.match true

/-
This breaks because of less case splitting, and moving the case splitting to
the contradiction phase is not enough, as `contradiction` does not look more than
one constructor deep:
```
example (n : Nat) (h : n.succ = 0) : False := by contradiction
example (n : Nat) (h : Int.ofNat n.succ = 0) : False := by contradiction
```
-/

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
