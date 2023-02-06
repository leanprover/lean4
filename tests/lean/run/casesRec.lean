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
    have := deq a₁ b₁
    have := deq a₂ b₂
    exact
      if h₁ : a₁ = b₁ then
        if h₂ : a₂ = b₂ then
          isTrue (by rw [h₁,h₂])
        else
          isFalse (fun h => by cases h; cases (h₂ rfl))
      else
        isFalse (fun h => by cases h; cases (h₁ rfl))

end Ex3
