open List

example : [3,1,4,2] ~ [2,4,1,3] := by grind

example (xs ys zs : List Nat) (h₁ : xs ⊆ ys) (h₂ : ys ~ zs) : xs ⊆ zs := by grind
example (xs ys zs : List Nat) (h₁ : xs <+ ys) (h₂ : ys ~ zs) : xs ⊆ zs := by grind
example (xs ys zs : List Nat) (h₁ : xs ~ ys) (h₂ : ys ~ zs) : xs ~ zs := by grind

example : List.range 10 ~ (List.range 5 ++ List.range' 5 5).reverse := by grind

variable [BEq α] [LawfulBEq α]

example (xs ys : List (List α)) (h : xs ~ ys) : xs.flatten ~ ys.flatten := by grind

example {l l' : List α} (hl : l ~ l') (_ : l'.Nodup) : l.Nodup := by grind

example {a b : α} {as bs : List α} :
    a :: as ++ b :: bs ~ b :: as ++ a :: bs := by grind

example (x y : α) (l : List α) :
    List.insert x (List.insert y l) ~ List.insert y (List.insert x l) := by grind
