def f : Nat → Nat → Nat
  | 0,   y   => y
  | x+1, y+1 => f (x-2) y
  | x+1, 0   => 0

example : f 0 y = y :=
  rfl -- Error, it does not hold by reflexivity since the recursion is on `y`

example : f 0 0 = 0 := rfl

example : f 0 (y+1) = y+1 := rfl

inductive Vector' (α : Type u) : Nat → Type u where
  | nil  : Vector' α 0
  | cons : α → Vector' α n → Vector' α (n+1)

namespace Vector'
  def insert (a: α): Fin (n+1) → Vector' α n → Vector' α (n+1)
  | ⟨0  , _⟩,        xs => cons a   xs
  | ⟨i+1, h⟩, cons x xs => cons x $ xs.insert a ⟨i, Nat.lt_of_succ_lt_succ h⟩

  theorem insert_at_0_eq_cons1 (a: α) (v: Vector' α n):  v.insert a ⟨0, Nat.zero_lt_succ n⟩ = cons a v :=
    rfl -- Error, it does not hold by reflexivity because the recursion is on v

  example (a : α) :  nil.insert a ⟨0, by simp +arith⟩ = cons a nil :=
    rfl

  example (a : α) (b : α) (bs : Vector' α n) :  (cons b bs).insert a ⟨0, by simp +arith⟩ = cons a (cons b bs) :=
    rfl

  theorem insert_at_0_eq_cons2 (a: α) (v: Vector' α n):  v.insert a ⟨0, Nat.zero_lt_succ n⟩ = cons a v := by
    rw [insert]

  theorem insert_at_0_eq_cons3 (a: α) (v: Vector' α n):  v.insert a ⟨0, Nat.zero_lt_succ n⟩ = cons a v := by
    simp only [insert]

end Vector'
