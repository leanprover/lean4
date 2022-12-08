namespace Ex1
def f (x : Nat) : Nat := by
  cases x with
  | zero => exact 1
  | succ x' =>
    apply Nat.mul 2
    exact f x'

#eval f 10

example : f x.succ = 2 * f x := rfl
end Ex1

namespace Ex2
inductive Foo where
  | mk : List Foo → Foo

mutual
def g (x : Foo) : Nat := by
  cases x with
  | mk xs => exact gs xs

def gs (xs : List Foo) : Nat := by
  cases xs with
  | nil => exact 1
  | cons x xs =>
    apply Nat.add
    exact g x
    exact gs xs
end
end Ex2

namespace Ex3

inductive Foo where
  | a | b | c
  | pair: Foo × Foo → Foo

def Foo.deq (a b : Foo) : Decidable (a = b) := by
  cases a <;> cases b
  any_goals apply isFalse Foo.noConfusion
  any_goals apply isTrue rfl
  case pair a b =>
    let (a₁, a₂) := a
    let (b₁, b₂) := b
    exact match deq a₁ b₁, deq a₂ b₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁,h₂])
    | isFalse h₁, _ => isFalse (fun h => by cases h; cases (h₁ rfl))
    | _, isFalse h₂ => isFalse (fun h => by cases h; cases (h₂ rfl))

end Ex3
