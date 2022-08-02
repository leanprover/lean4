namespace Ex1

variable {α : Type}
variable [Add α]
variable (α)
def f (a : α) := a + a
#check f Nat 5
variable {α}
def g (b : α) := b
#check g 5
#check @f
#check @g
end Ex1

namespace Ex2

variable {α β : Type}
variable (α)
def f (a : α) := a
def g (b : β) := b
#check f Nat 5
#check g 5
#check @f
#check @g
variable (α)
end Ex2

namespace Ex3

variable {α : Type}
variable (f : α → α)
variable (α)
def g (a : α) := f a
#check @g
variable {f}
def h (a : α) := f a
#check @h
end Ex3

namespace Ex4

variable {α β : Type}
variable (α γ)
def g (a : α) (b : β) (c : γ) := (a, b, c)
#check g Nat Bool 10 "hello" true
end Ex4

namespace Ex5

variable [i : Add α]
variable (i) -- Error

end Ex5

namespace Ex6

variable (a : Nat)
variable (h : a = a := rfl)
variable {h} -- Error

end Ex6
