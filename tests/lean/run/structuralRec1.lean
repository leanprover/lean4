new_frontend

def map {α β} (f : α → β) : List α → List β
| []    => []
| a::as => f a :: map f as

theorem ex1 : map Nat.succ [1] = [2] :=
rfl

theorem ex2 : map Nat.succ [] = [] :=
rfl

theorem ex3 (a : Nat) : map Nat.succ [a] = [Nat.succ a] :=
rfl

theorem ex4 {α β} (f : α → β) (a : α) (as : List α) : map f (a::as) = (f a) :: map f as :=
rfl

theorem ex5 {α β} (f : α → β) : map f [] = [] :=
rfl
