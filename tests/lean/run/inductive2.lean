

mutual
universe u
variable (α : Type u)

inductive isEvenList : List α → Prop
| nil {}  : isEvenList []
| cons (h : α) {t : List α} : isOddList t → isEvenList (h::t)

inductive isOddList : List α → Prop
| cons (h : α) {t : List α} : isEvenList t → isOddList (h::t)
end

#check @isEvenList.nil
#check @isEvenList.cons
#check @isOddList.cons
#check isEvenList.nil Nat
#check isEvenList.cons 1 $ isOddList.cons 2 $ isEvenList.nil Nat
