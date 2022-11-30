mutual

inductive IsEvenList : List α → Prop
| nil (α)  : IsEvenList (α := α) []
| cons (h : α) {t : List α} : IsOddList t → IsEvenList (h::t)

inductive IsOddList : List α → Prop
| cons (h : α) {t : List α} : IsEvenList t → IsOddList (h::t)
end
set_option pp.explicit true
#print IsEvenList
#check @IsEvenList.nil
#check @IsEvenList.cons
#check @IsOddList.cons
#check IsEvenList.nil Nat
#check IsEvenList.cons 1 $ IsOddList.cons 2 $ IsEvenList.nil Nat
