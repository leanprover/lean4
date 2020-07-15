new_frontend

inductive L1.{u} (α : Type u)
| nil
| cons : α → L1 → L1

#check L1
#check @L1.cons

inductive L2.{u} (α : Type u)
| nil
| cons (head : α) (tail : L2)

#check @L2.cons

universes u v
variable (α : Type u)

inductive A (β : Type v)
| nil {}
| protected cons : α → β → A → A

#check @A.cons
#check A.nil Nat Bool

mutual
  inductive isEven : Nat → Prop
  | z : isEven 0
  | s (n : Nat) : isOdd n → isEven (n+1)

  inductive isOdd : Nat → Prop
  | s (n : Nat) : isEven n → isOdd (n+1)
end

#check isEven
#check isOdd.s
#check @isEven.rec

inductive V (α : Type _) : Nat → Type _
| nil  : V 0
| cons {n : Nat} : α → V n → V (n+1)

#check @V.nil
#check @V.cons
#check @V.rec
