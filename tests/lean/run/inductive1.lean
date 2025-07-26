inductive L1.{u} (α : Type u)
| nil
| cons : α → L1 α → L1 α

#check L1
#check @L1.cons

inductive L2.{u} (α : Type u)
| nil
| cons (head : α) (tail : L2 α)

#check @L2.cons

universe u v
variable (α : Type u)

inductive A (β : Type v)
| nil
| protected cons : α → β → A β → A β

#check @A.cons
#check A.nil (α := Nat) (β := Bool)

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
| nil  : V α 0
| cons {n : Nat} : α → V α n → V α (n+1)

#check @V.nil
#check @V.cons
#check @V.rec
#check @V.noConfusion
#check @V.brecOn
#check @V.casesOn
#check @V.recOn
#check @V.below

class inductive Dec (p : Prop) : Type
| isTrue  (h : p)
| isFalse (h : Not p)

instance tst : Dec True :=
Dec.isTrue True.intro

#check tst

variable (β : Type _)

inductive T1
| mk : β → β → T1

#check @T1.mk


inductive MyEq {α : Type} (a : α) : α → Prop
| refl : MyEq a a

#check @MyEq.refl

inductive ListLast {α : Type u} : List α → Type u
| empty    : ListLast []
| nonEmpty : (as : List α) → (a : α) → ListLast (as ++ [a])

-- make sure to instantiate mvars in constructors
inductive Test : Nat → Type
| mk : Test ((fun n => n.succ) Nat.zero)

inductive SortedMap {α : Type u} {β : Type v} [LT α] : List (α × β) → Prop
| nil : SortedMap []
| cons : ∀ (k : α) (v : β) (l : List (α × β)),
         SortedMap l →
         SortedMap ((k,v)::l)
